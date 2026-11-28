import Langlands.AlgebraicGeometry.FiniteEtale.GeometricContinuousActionEquivalenceProof
import Langlands.AlgebraicGeometry.FiniteEtale.AffineQuotientCoconeProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricPathProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Torsor covers attached to finite abelian quotients of the fundamental group

For a connected locally Noetherian scheme `S` with a geometric point `s`, every continuous
homomorphism `χ` with open kernel from the finite étale fundamental group `π₁(S, s)` to a finite
commutative group `C` is realized by a cover of `S` with an action of `C` whose geometric fibre
at `s` is identified with `C`, the fundamental group acting through `χ` and `C` by translation.
For an affine `S` and a diagram `D : SingleObj C ⥤ Cover S` on which `C` acts simply
transitively on the geometric fibre, the `C`-invariants of the ring of the cover are the ring of
`S`, and over every maximal ideal of `Γ(S, ⊤)` there is a point of the cover with values in a
field that no nontrivial element of `C` fixes.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped FintypeCatDiscrete

namespace Langlands.AlgebraicGeometry.FiniteEtale

section Torsor

variable {S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S] {Ω : Type u} [Field Ω]
  [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  {C : Type u} [CommGroup C] [Finite C]

/-- **Torsor covers.** A continuous homomorphism `χ : π₁(S, s) → C` with open kernel to a finite
commutative group is realized by a diagram `D : SingleObj C ⥤ Cover S` and a bijection `φ` of the
geometric fibre of its cover with `C` under which `g ∈ π₁(S, s)` acts by multiplication by
`χ g` and `c ∈ C` acts by multiplication by `c`. -/
theorem exists_torsor_cover (χ : FundamentalGroup s hs →* C)
    (hχ : IsOpen (χ.ker : Set (FundamentalGroup s hs))) :
    ∃ (D : SingleObj C ⥤ Cover S) (φ : Fiber s (D.obj (SingleObj.star C)) ≃ C),
      (∀ (g : FundamentalGroup s hs) (y : Fiber s (D.obj (SingleObj.star C))),
        φ (g • y) = χ g * φ y) ∧
      ∀ (c : C) (y : Fiber s (D.obj (SingleObj.star C))),
        φ (y ≫ (D.map (SingleObj.toEnd C c).asHom).hom) = c * φ y := by
  obtain ⟨hG, hF⟩ := geometricGaloisFiberFunctor s hs
  let : GaloisCategory (Cover S) := hG
  let : PreGaloisCategory.FiberFunctor (fiberFunctor s hs) := hF
  let : Fintype C := Fintype.ofFinite C
  let : MulAction (FundamentalGroup s hs) C := MulAction.compHom C χ
  let : TopologicalSpace C := ⊥
  have : DiscreteTopology C := ⟨rfl⟩
  have hcs : ContinuousSMul (FundamentalGroup s hs) C := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    convert hχ using 2
    ext g
    simp [MulAction.mem_stabilizer_iff, MulAction.compHom_smul_def]
  let X₀ : Action FintypeCat.{u} (FundamentalGroup s hs) :=
    Action.FintypeCat.ofMulAction (FundamentalGroup s hs) (FintypeCat.of C)
  have hX₀ : X₀.IsContinuous := by
    rw [Action.isContinuous_def]
    exact hcs.continuous_smul
  let X : ContAction FintypeCat.{u} (FundamentalGroup s hs) := ⟨X₀, hX₀⟩
  let mulC : C → C → C := fun c x => c * x
  let mhom : C → (X ⟶ X) := fun c => ObjectProperty.homMk
    { hom := FintypeCat.homMk (mulC c)
      comm := fun g => by
        refine FintypeCat.hom_ext _ _ (fun x => ?_)
        simp only [ConcreteCategory.comp_apply, FintypeCat.homMk_apply]
        change c * (χ g * @id C x) = χ g * (c * @id C x)
        exact mul_left_comm _ _ _ }
  have mhom_apply : ∀ (c : C) (x : C), (mhom c).hom.hom x = c * x := fun _ _ => rfl
  let m : C →* End X :=
    { toFun := fun c => .of (mhom c)
      map_one' := by
        ext x
        exact one_mul (@id C x)
      map_mul' := fun c d => by
        ext x
        exact mul_assoc c d (@id C x) }
  let E := (PreGaloisCategory.functorToContAction (fiberFunctor s hs)).asEquivalence
  let D : SingleObj C ⥤ Cover S := SingleObj.functor m ⋙ E.inverse
  let φf : Fiber s (D.obj (SingleObj.star C)) → C := fun y => (E.counitIso.app X).hom.hom.hom y
  let ψf : C → Fiber s (D.obj (SingleObj.star C)) := fun x => (E.counitIso.app X).inv.hom.hom x
  refine ⟨D, ⟨φf, ψf, fun y => ?_, fun x => ?_⟩, fun g y => ?_, fun c y => ?_⟩
  · change ((E.counitIso.app X).hom ≫ (E.counitIso.app X).inv).hom.hom.hom y = y
    rw [Iso.hom_inv_id]
    rfl
  · change ((E.counitIso.app X).inv ≫ (E.counitIso.app X).hom).hom.hom.hom x = x
    rw [Iso.inv_hom_id]
    rfl
  · have h := congrArg (fun f => f y) ((E.counitIso.app X).hom.hom.comm g)
    simp only [ConcreteCategory.comp_apply] at h
    exact h
  · have h := congrArg (fun f => f.hom.hom y) (E.counitIso.hom.naturality (mhom c))
    exact h

end Torsor

section Quotient

variable {S : Scheme.{u}} [IsAffine S] [ConnectedSpace S] [IsLocallyNoetherian S]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
  {C : Type u} [Group C] [Finite C] (D : SingleObj C ⥤ Cover S)

/-- If `C` acts transitively on the nonempty geometric fibre of the cover of `D`, the map from
`Γ(S, ⊤)` to the ring of `C`-invariants of the cover is bijective. -/
theorem bijective_algebraMap_quotientRing
    (hne : Nonempty (Fiber s (D.obj (SingleObj.star C))))
    (htrans : ∀ y z : Fiber s (D.obj (SingleObj.star C)),
      ∃ c : C, z = y ≫ (D.map (SingleObj.toEnd C c).asHom).hom) :
    Function.Bijective (algebraMap Γ(S, ⊤) (quotientRing D)) := by
  have hs := geometricFiberFinite s
  obtain ⟨hG, hF⟩ := geometricGaloisFiberFunctor s hs
  let : GaloisCategory (Cover S) := hG
  let : PreGaloisCategory.FiberFunctor (fiberFunctor s hs) := hF
  let I : Cover S := cover (𝟙 S)
  let q : quotientCover D ⟶ I :=
    ObjectProperty.homMk (Over.homMk (quotientStructure D) (by simp [I, cover]; rfl))
  have hsub : Subsingleton (Fiber s (quotientCover D)) := by
    constructor
    intro u v
    obtain ⟨y, rfl⟩ := quotientCocone_surjective D s u
    obtain ⟨z, rfl⟩ := quotientCocone_surjective D s v
    obtain ⟨c, hc⟩ := htrans y z
    exact (quotientCocone_orbit D s y z).mpr ⟨c, hc⟩
  have hsubI : Subsingleton (Fiber s I) := by
    constructor
    intro p p'
    apply Over.OverMorphism.ext
    have hp : p.left ≫ 𝟙 _ = s := Over.w p
    have hp' : p'.left ≫ 𝟙 _ = s := Over.w p'
    simpa using hp.trans hp'.symm
  have hbij : Function.Bijective ((fiberFunctor s hs).map q) := by
    constructor
    · intro u v _
      exact @Subsingleton.elim (Fiber s (quotientCover D)) hsub u v
    · intro p
      obtain ⟨y⟩ := hne
      exact ⟨(pointFunctor s).map ((quotientCocone D).ι.app (SingleObj.star C)) y,
        @Subsingleton.elim (Fiber s I) hsubI _ _⟩
  have : IsIso ((fiberFunctor s hs).map q) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : IsIso q := isIso_of_reflects_iso q (fiberFunctor s hs)
  have hq : IsIso (quotientStructure D) :=
    Functor.map_isIso (inclusion S ⋙ Over.forget S) q
  have h2 : IsIso (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (quotientRing D)))) := by
    have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (quotientRing D))) ≫
        S.isoSpec.inv) := hq
    exact IsIso.of_isIso_comp_right _ S.isoSpec.inv
  exact isIso_SpecMap_iff.mp h2

/-- If `C` acts transitively on the nonempty geometric fibre of the cover of `D`, every
`C`-invariant element of the ring of the cover comes from `Γ(S, ⊤)`. -/
theorem exists_algebraMap_eq_of_forall_coverAction_eq
    (hne : Nonempty (Fiber s (D.obj (SingleObj.star C))))
    (htrans : ∀ y z : Fiber s (D.obj (SingleObj.star C)),
      ∃ c : C, z = y ≫ (D.map (SingleObj.toEnd C c).asHom).hom)
    (b : coverRing D) (hb : ∀ c : C, (coverAction D c).hom b = b) :
    ∃ r : Γ(S, ⊤), algebraMap Γ(S, ⊤) (coverRing D) r = b := by
  obtain ⟨r, hr⟩ := (bijective_algebraMap_quotientRing s D hne htrans).2
    ⟨b, (mem_quotientRing_iff D b).mpr hb⟩
  exact ⟨r, congrArg Subtype.val hr⟩

omit [Finite C] in
/-- If `C` acts freely on the nonempty geometric fibre of the cover of `D`, then over every
maximal ideal `𝔪` of `Γ(S, ⊤)` there is a ring map `φ` from the ring of the cover to a field,
killing `𝔪`, with `φ ∘ c ≠ φ` for every `c ≠ 1` in `C`. -/
theorem exists_free_residue_point
    (hne : Nonempty (Fiber s (D.obj (SingleObj.star C))))
    (hfree : ∀ (y : Fiber s (D.obj (SingleObj.star C))) (c : C),
      y ≫ (D.map (SingleObj.toEnd C c).asHom).hom = y → c = 1)
    (𝔪 : Ideal Γ(S, ⊤)) [𝔪.IsMaximal] :
    ∃ (K : Type u) (_ : Field K) (φ : coverRing D →+* K),
      (∀ r ∈ 𝔪, φ (algebraMap Γ(S, ⊤) (coverRing D) r) = 0) ∧
        ∀ c : C, c ≠ 1 → φ.comp (coverAction D c).hom ≠ φ := by
  have hs := geometricFiberFinite s
  let := Ideal.Quotient.field 𝔪
  let K := AlgebraicClosure (Γ(S, ⊤) ⧸ 𝔪)
  let f₀ : Γ(S, ⊤) →+* K := (algebraMap (Γ(S, ⊤) ⧸ 𝔪) K).comp (Ideal.Quotient.mk 𝔪)
  let s' : Spec (.of K) ⟶ S := (affinePointEquiv S (.of K)).symm (CommRingCat.ofHom f₀)
  have hs' := geometricFiberFinite s'
  obtain ⟨e⟩ := geometricPathExists s s' hs hs'
  obtain ⟨y⟩ := hne
  let y' : Fiber s' (D.obj (SingleObj.star C)) := (e.hom.app _) y
  refine ⟨K, inferInstance, (fiberRingHom D s' y').hom, fun r hr => ?_, fun c hc h => hc ?_⟩
  · have h1 := congrArg (fun φ => CommRingCat.Hom.hom φ r) (appTop_comp_fiberRingHom D s' y')
    simp only [Equiv.apply_symm_apply, s'] at h1
    change (fiberRingHom D s' y').hom
      ((D.obj (SingleObj.star C)).obj.hom.appTop.hom r) = 0
    rw [← CommRingCat.comp_apply, h1]
    simp [f₀, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  · apply hfree y c
    have h2 : fiberRingHom D s'
        ((pointFunctor s').map (D.map (SingleObj.toEnd C c).asHom) y') = fiberRingHom D s' y' := by
      rw [fiberRingHom_map]
      ext b
      exact congrArg (fun φ : coverRing D →+* K => φ b) h
    have h3 := fiberRingHom_injective D s' h2
    have hn := congrArg (fun f => f y') (e.inv.naturality (D.map (SingleObj.toEnd C c).asHom))
    have hy := congrArg (fun f => f y) (e.hom_inv_id_app (D.obj (SingleObj.star C)))
    simp only [ConcreteCategory.comp_apply] at hn hy
    have hy' : e.inv.app (D.obj (SingleObj.star C)) y' = y := hy
    have h4 : (fiberFunctor s' hs').map (D.map (SingleObj.toEnd C c).asHom) y' = y' := h3
    rw [h4, hy'] at hn
    exact hn.symm

end Quotient

end Langlands.AlgebraicGeometry.FiniteEtale
