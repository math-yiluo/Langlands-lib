/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomologyBaseChangeReduced
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.RfPerfect

/-!
# The base change maps of the higher direct images

Consider a cartesian square of schemes with affine bases `S = Spec A` and `T = Spec B`
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
a quasi-coherent `𝒪_X`-module `ℱ` and a finite cover `U` of `X` by affine opens. The Čech
complex `Č(U, ℱ)` computes `Γ(S, R^q f_* ℱ)` and `Č(g'⁻¹ U, g'^* ℱ) = B ⊗[A] Č(U, ℱ)` computes
`Γ(T, R^q f'_* g'^* ℱ)`. The **base change map** in degree `q`
(`AlgebraicGeometry.Scheme.Modules.cechBaseChangeMap`)
```
B ⊗[A] H^q(Č(U, ℱ)) ⟶ H^q(Č(g'⁻¹ U, g'^* ℱ)),   b ⊗ [z] ↦ b • [g'^* z]
```
is the canonical map `g^* R^q f_* ℱ ⟶ R^q f'_* g'^* ℱ` on global sections. For `T` the
spectrum of the residue field `κ(t)` of a point `t` it is the base change map
`φ^q(t) : R^q f_* ℱ ⊗ κ(t) ⟶ H^q(X_t, ℱ_t)` of the semicontinuity theorem.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.bijective_cechBaseChangeMap_of_forall_specializes`
  (Grauert): for `f` proper of finite presentation, `ℱ` of finite presentation and flat over `S`,
  and `S` reduced and noetherian, the base change map at a point `t` is bijective as soon as the
  fibre dimension `h^q` is the same at `t` and at all its generisations.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct DerivedCategory Module

namespace AlgebraicGeometry.Scheme.Modules

section Map

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules)
  [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
  {ι : Type u} (U : ι → X.Opens) [IsAffine S] [IsAffine T]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι]
  (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))

/-- **The base change map** `B ⊗[A] H^q(Č(U, ℱ)) ⟶ H^q(Č(g'⁻¹ U, g'^* ℱ))` of the Čech
cohomology for a cartesian square with affine bases `S = Spec A` and `T = Spec B`,
`b ⊗ [z] ↦ b • [g'^* z]`: the base change map on homology
(`CategoryTheory.ShortComplex.homologyBaseChange`) followed by the identification
`B ⊗[A] Č(U, ℱ) ≅ Č(g'⁻¹ U, g'^* ℱ)`
(`AlgebraicGeometry.Scheme.Modules.cechModuleComplexBaseChangeIso`).

For `T = Spec κ(t)` this is the base change map `φ^q(t) : R^q f_* ℱ ⊗ κ(t) ⟶ H^q(X_t, ℱ_t)`.

(blueprint: `lemma-triviality-fibres--2`, part (1)) -/
noncomputable def cechBaseChangeMap (q : ℤ) :
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] (cechModuleComplex f ℱ U).homology q →ₗ[Γ(T, ⊤)]
      (cechModuleComplex f' ((pullback g').obj ℱ) (fun i ↦ g' ⁻¹ᵁ U i)).homology q :=
  (HomologicalComplex.homologyMap (cechModuleComplexBaseChangeIso H ℱ hg U hU).hom q).hom ∘ₗ
    ((cechModuleComplex f ℱ U).sc q).homologyBaseChange Γ(T, ⊤)

lemma bijective_cechBaseChangeMap_iff (q : ℤ) :
    Function.Bijective (cechBaseChangeMap H ℱ hg U hU q) ↔
      Function.Bijective (((cechModuleComplex f ℱ U).sc q).homologyBaseChange Γ(T, ⊤)) := by
  let e := (HomologicalComplex.homologyMapIso (cechModuleComplexBaseChangeIso H ℱ hg U hU)
    q).toLinearEquiv
  change Function.Bijective (e ∘ _) ↔ _
  exact e.bijective.of_comp_iff' _

end Map

section Perfect

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)
  [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsProper f] [LocallyOfFinitePresentation f]
  [ℱ.IsFinitePresentation]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι] [Nonempty ι]
  (hU : ∀ i, IsAffineOpen (U i)) (hU' : iSup U = ⊤)

include hU hU' in
/-- The Čech complex of a proper flat family receives a quasi-isomorphism from a bounded complex
of finitely generated projective modules, which stays a quasi-isomorphism after any base
change. -/
lemma exists_quasiIso_cechModuleComplex (hℱ : ℱ.IsFlatOver f) :
    ∃ (P : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ) (φ : P ⟶ cechModuleComplex f ℱ U),
      (∀ i, Module.Projective Γ(S, ⊤) (P.X i) ∧ Module.Finite Γ(S, ⊤) (P.X i)) ∧
      QuasiIso φ ∧ ∀ (B : Type u) [CommRing B] [Algebra Γ(S, ⊤) B],
        QuasiIso (((ModuleCat.baseChange Γ(S, ⊤) B).mapHomologicalComplex _).map φ) := by
  have := Fintype.ofFinite ι
  have hC := isPerfect_Q_cechModuleComplex_of_isNoetherianRing f ℱ U hU hU' hℱ
  obtain ⟨e₀⟩ := nonempty_Q_cechModuleComplexTrunc_iso f ℱ U hU hU'
  obtain ⟨P, a', b', _, _, hPfin, ⟨e⟩⟩ := hC.of_iso e₀.symm
  have : ∀ n, Projective (P.X n) := fun n ↦
    (IsProjective.iff_projective (P.X n)).1 (hPfin n).1
  have := CochainComplex.isKProjective_of_projective P b'
  obtain ⟨α, hα⟩ := exists_quasiIso_of_isKProjective e.symm
  have hPflat (i : ℤ) : Module.Flat Γ(S, ⊤) (P.X i) := by
    have := (hPfin i).1
    infer_instance
  have hK := flat_cechModuleComplexTrunc_X f ℱ U hU hU' hℱ
  have := quasiIso_ιTruncLE_cechModuleComplex f ℱ U hU hU'
  refine ⟨P, α ≫ (cechModuleComplex f ℱ U).ιTruncLE _, hPfin, inferInstance, fun B _ _ ↦ ?_⟩
  -- the mapping cone of `α` vanishes in high degrees
  have hcone (k : ℤ) (hk : max b' ((Fintype.card ι : ℤ) - 1) + 1 ≤ k) :
      Module.Flat Γ(S, ⊤)
        (LinearMap.ker ((CochainComplex.mappingCone α).d k (k + 1)).hom) := by
    have hz : IsZero ((CochainComplex.mappingCone α).X k) :=
      (CochainComplex.mappingCone.isZero_X_iff α k).2
        ⟨P.isZero_of_isStrictlyLE b' (k + 1) (by lia),
          (cechModuleComplexTrunc f ℱ U).isZero_of_isStrictlyLE ((Fintype.card ι : ℤ) - 1) k
            (by lia)⟩
    have : Subsingleton ((CochainComplex.mappingCone α).X k) :=
      ModuleCat.subsingleton_of_isZero hz
    infer_instance
  have := CochainComplex.quasiIso_map_baseChange B α hPflat hK hcone
  have := quasiIso_map_baseChange_ιTruncLE_cechModuleComplex f ℱ U hU hU' hℱ B
  rw [Functor.map_comp]
  infer_instance

include hU hU' in
/-- **Grauert's theorem on the Čech complex, algebraically.** In the situation of
`AlgebraicGeometry.Scheme.Modules.exists_quasiIso_cechModuleComplex`, with `A = Γ(S, ⊤)`
reduced, let `K` be a field over `A`, with kernel `t`. If the dimension of `H^q(L ⊗[A] Č(U, ℱ))`
is the same for `L = K` and for every field `L` over `A` whose kernel is contained in `t`, then
the base change map `K ⊗[A] H^q(Č(U, ℱ)) ⟶ H^q(K ⊗[A] Č(U, ℱ))` is bijective. -/
theorem bijective_homologyBaseChange_cechModuleComplex [_root_.IsReduced Γ(S, ⊤)]
    (hℱ : ℱ.IsFlatOver f) (q : ℤ) (K : Type u) [Field K] [Algebra Γ(S, ⊤) K]
    (h : ∀ (L : Type u) [Field L] [Algebra Γ(S, ⊤) L],
      RingHom.ker (algebraMap Γ(S, ⊤) L) ≤ RingHom.ker (algebraMap Γ(S, ⊤) K) →
        finrank L (((cechModuleComplex f ℱ U).sc q).baseChange L).homology =
          finrank K (((cechModuleComplex f ℱ U).sc q).baseChange K).homology) :
    Function.Bijective (((cechModuleComplex f ℱ U).sc q).homologyBaseChange K) := by
  obtain ⟨P, φ, hP, _, hφ⟩ := exists_quasiIso_cechModuleComplex f ℱ U hU hU' hℱ
  rw [← HomologicalComplex.bijective_homologyBaseChange_iff_of_quasiIsoAt K φ q]
  have : Module.Finite Γ(S, ⊤) (P.sc q).X₁ := (hP _).2
  have : Module.Finite Γ(S, ⊤) (P.sc q).X₂ := (hP _).2
  have : Module.Finite Γ(S, ⊤) (P.sc q).X₃ := (hP _).2
  have : Module.Projective Γ(S, ⊤) (P.sc q).X₃ := (hP _).1
  refine (P.sc q).bijective_homologyBaseChange_of_finrank_eq K fun L _ _ hL ↦ ?_
  rw [← HomologicalComplex.finrank_homology_baseChange_eq_of_quasiIsoAt φ q L,
    ← HomologicalComplex.finrank_homology_baseChange_eq_of_quasiIsoAt φ q K]
  exact h L hL

end Perfect

section Fibre

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)
  [IsAffine S] [IsProper f] [ℱ.IsFinitePresentation]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι]
  (hU : ∀ i, IsAffineOpen (U i)) (hU' : iSup U = ⊤)

include hU hU' in
/-- **The fibre dimension from the Čech complex.** For a field point `g : Spec K ⟶ S` and `x` the
point of `Spec K`, the fibre dimension `h^q` of `ℱ` at `g x` is the dimension of
`H^q(Γ(Spec K, ⊤) ⊗[A] Č(U, ℱ))`: this is the Čech complex of the pullback of `ℱ` to
`X ×_S Spec K`, which computes its cohomology. -/
theorem finrank_homology_cechModuleComplex_baseChange_eq_hFiber (K : Type u) [Field K]
    (g : Spec (.of K) ⟶ S) [Algebra Γ(S, ⊤) Γ(Spec (.of K), ⊤)]
    (hg : algebraMap Γ(S, ⊤) Γ(Spec (.of K), ⊤) = g.appTop.hom) (q : ℕ) (x : Spec (.of K)) :
    finrank Γ(Spec (.of K), ⊤)
        (((cechModuleComplex f ℱ U).sc q).baseChange Γ(Spec (.of K), ⊤)).homology =
      ℱ.hFiber f q (g.base x) := by
  have sq := IsPullback.of_hasPullback f g
  set f' := pullback.snd f g
  set g' := pullback.fst f g
  have : IsSeparated f' := MorphismProperty.of_isPullback sq ‹IsProper f›.toIsSeparated
  have : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
  have hUK (i : ι) : IsAffineOpen (g' ⁻¹ᵁ U i) :=
    isAffineOpen_preimage_of_isPullback sq (isAffineOpen_top S) (by simp) (by simp) (hU i)
  have hUK' : iSup (fun i ↦ g' ⁻¹ᵁ U i) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hU', Scheme.Hom.preimage_top]
  -- the Čech complex of the pullback of `ℱ` is the base change of that of `ℱ`
  refine ((HomologicalComplex.homologyMapIso (cechModuleComplexBaseChangeIso sq ℱ hg U
    (isAffineOpen_iInf_of_isSeparated f U hU)) q).toLinearEquiv.finrank_eq).trans ?_
  obtain ⟨e, he⟩ := exists_homology_cechModuleComplex_equiv_H f' ((pullback g').obj ℱ)
    (fun i ↦ g' ⁻¹ᵁ U i) hUK hUK' q
  rw [← hFiber_pullback_of_isPullback f ℱ g g' f' sq q x,
    hFiber_eq_finrankH f' ((pullback g').obj ℱ) q x]
  let : (Limits.pullback f g).Over (Spec (.of K)) := ⟨f'⟩
  refine (congrArg Cardinal.toNat (rank_eq_of_equiv_equiv _ e.symm
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv) fun c y ↦ ?_)).symm
  apply e.injective
  rw [AddEquiv.apply_symm_apply, he, AddEquiv.apply_symm_apply,
    smul_H_eq_globalSectionsRingHom_smul]
  rfl

/-- Of two field points of an affine scheme, the first generalises the second as soon as every
global function vanishing at the first vanishes at the second. -/
lemma specializes_of_ker_appTop_le {R R' : CommRingCat.{u}} (hR : IsField Γ(Spec R, ⊤))
    (hR' : IsField Γ(Spec R', ⊤)) (g₁ : Spec R ⟶ S) (g₂ : Spec R' ⟶ S)
    (h : RingHom.ker g₁.appTop.hom ≤ RingHom.ker g₂.appTop.hom) (x₁ : Spec R) (x₂ : Spec R') :
    g₁.base x₁ ⤳ g₂.base x₂ := by
  rw [specializes_iff_forall_open]
  intro s hs hx
  obtain ⟨_, ⟨a, rfl⟩, ha, hle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 (isBasis_basicOpen S) (U := ⟨s, hs⟩) hx
  refine hle ((Scheme.Hom.appTop_ne_zero_iff_mem_basicOpen hR g₁ a x₁).1 fun h0 ↦ ?_)
  exact (Scheme.Hom.appTop_ne_zero_iff_mem_basicOpen hR' g₂ a x₂).2 ha
    (RingHom.mem_ker.1 (h (RingHom.mem_ker.2 h0)))

/-- The field point `Spec L ⟶ S` of an affine scheme defined by a ring homomorphism
`Γ(S, ⊤) ⟶ L`. -/
noncomputable abbrev fieldPoint (L : Type u) [Field L] [Algebra Γ(S, ⊤) L] : Spec (.of L) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) L)) ≫ S.isoSpec.inv

lemma fieldPoint_appTop (L : Type u) [Field L] [Algebra Γ(S, ⊤) L] (a : Γ(S, ⊤)) :
    (fieldPoint (S := S) L).appTop a = (Scheme.ΓSpecIso (.of L)).inv (algebraMap Γ(S, ⊤) L a) := by
  have h₁ : S.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(S, ⊤)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv]
    rfl
  have h₂ : (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) L))).appTop =
      (Scheme.ΓSpecIso Γ(S, ⊤)).hom ≫ CommRingCat.ofHom (algebraMap Γ(S, ⊤) L) ≫
        (Scheme.ΓSpecIso _).inv := by
    rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  change (S.isoSpec.inv.appTop ≫ (Spec.map _).appTop) a = _
  rw [h₂, ← Category.assoc, ← Category.assoc, h₁, Category.id_comp]
  rfl

include hU hU' in
/-- **Grauert's theorem for the Čech complex over an affine base.** Let `f : X ⟶ S` be proper of
finite presentation over a reduced noetherian affine scheme `S = Spec A`, `ℱ` a quasi-coherent
`𝒪_X`-module of finite presentation, flat over `S`, and `U` a finite cover of `X` by affine
opens. Let `g : Spec K ⟶ S` be a field point, through a point `s = g x`. If the fibre dimension
`h^q` takes the same value at all generisations of `s` as at `s`, then the base change map
`Γ(Spec K, ⊤) ⊗[A] H^q(Č(U, ℱ)) ⟶ H^q(Č(g'⁻¹ U, g'^* ℱ))` is bijective.

(blueprint: `lemma-triviality-fibres--2`, part (3), `lemma-triviality-fibres--2`) -/
theorem bijective_cechBaseChangeMap_of_forall_specializes [IsReduced S]
    [IsNoetherianRing Γ(S, ⊤)]
    [LocallyOfFinitePresentation f] [Nonempty ι] (hℱ : ℱ.IsFlatOver f) (K : Type u) [Field K]
    (g : Spec (.of K) ⟶ S) [Algebra Γ(S, ⊤) Γ(Spec (.of K), ⊤)]
    (hg : algebraMap Γ(S, ⊤) Γ(Spec (.of K), ⊤) = g.appTop.hom) (q : ℕ) (x : Spec (.of K))
    (h : ∀ s : S, s ⤳ g.base x → ℱ.hFiber f q s = ℱ.hFiber f q (g.base x)) :
    Function.Bijective (cechBaseChangeMap (IsPullback.of_hasPullback f g) ℱ hg U
      (isAffineOpen_iInf_of_isSeparated f U hU) q) := by
  have := Fintype.ofFinite ι
  have hK : IsField Γ(Spec (.of K), ⊤) := isField_Γ_Spec (Field.toIsField K)
  let : Field Γ(Spec (.of K), ⊤) := hK.toField
  rw [bijective_cechBaseChangeMap_iff]
  refine bijective_homologyBaseChange_cechModuleComplex f ℱ U hU hU' hℱ q _ fun L _ _ hL ↦ ?_
  have hL' : IsField Γ(Spec (.of L), ⊤) := isField_Γ_Spec (Field.toIsField L)
  let : Field Γ(Spec (.of L), ⊤) := hL'.toField
  let : Algebra Γ(S, ⊤) Γ(Spec (.of L), ⊤) := (fieldPoint (S := S) L).appTop.hom.toAlgebra
  let : Algebra L Γ(Spec (.of L), ⊤) := (Scheme.ΓSpecIso (.of L)).inv.hom.toAlgebra
  have : IsScalarTower Γ(S, ⊤) L Γ(Spec (.of L), ⊤) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ fieldPoint_appTop L a
  obtain ⟨y⟩ : Nonempty (Spec (.of L)) := inferInstance
  rw [← ((cechModuleComplex f ℱ U).sc q).finrank_homology_baseChange_eq_of_isScalarTower L
    Γ(Spec (.of L), ⊤), finrank_homology_cechModuleComplex_baseChange_eq_hFiber f ℱ U hU hU' L
      (fieldPoint L) rfl q y,
    finrank_homology_cechModuleComplex_baseChange_eq_hFiber f ℱ U hU hU' K g hg q x]
  refine h _ (specializes_of_ker_appTop_le hL' hK _ g ?_ y x)
  intro a ha
  rw [RingHom.mem_ker, ← hg]
  rw [RingHom.mem_ker] at ha
  change (fieldPoint L).appTop a = 0 at ha
  rw [fieldPoint_appTop, map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of L)).inv).1] at ha
  exact hL (RingHom.mem_ker.2 ha)

end Fibre

end AlgebraicGeometry.Scheme.Modules
