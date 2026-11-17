import Langlands.GroupScheme.Reductive.RelativeRootCommutatorIso
import Langlands.GroupScheme.Reductive.RelativeRootGroupBaseChange
import Langlands.GroupScheme.Reductive.QuadraticUnitFppfCover
import Langlands.GroupScheme.Reductive.QuadraticRootCharacterUnit
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Reductive.RelativeCommutatorBaseChange
import Langlands.GroupScheme.Reductive.CorootCommutator

/-! # Fppf-local commutators in actual relative root groups -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace Langlands.GroupScheme.LocalRootGroup
open RelativeDerived

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu : I → ℤ)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- A unit character difference makes every actual root value an abstract
commutator on the original test scheme. -/
theorem mem_commutator_incl_of_unit
    (t : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      (splitTorus (Spec (CommRingCat.of R)) I).X)
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J)
    (hmu0 : ∑ j, P.root α j * mu j = 0)
    (hmu : ∀ β : J, ∑ j, P.root β j * mu j = 0 →
      P.root β = P.root α ∨ P.root β = -P.root α)
    (hu : IsUnit ((show Γ(Spec (CommRingCat.of R), ⊤) from
      VectorGroup.charValue (splitTorus.exponentCharacter _ I (P.root α))
        (Over.mk (𝟙 _)) t) - 1))
    (Z : Over (Spec (CommRingCat.of R))) (x : Z ⟶ (Uc i mu (P.coroot α)).X) :
    x ≫ (incl i mu (P.coroot α)).hom.hom ∈ _root_.commutator (Z ⟶ G.X) := by
  let e := rootCommutatorIso i mu t hG hmax hP α hmu0 hmu hu
  let y := x ≫ e.inv
  have hy : y ≫ rootCommutatorMap i mu (P.coroot α) t = x := by
    change (x ≫ e.inv) ≫ e.hom = x
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he := rootCommutatorMap_apply i mu (P.coroot α) t y
  rw [hy] at he
  rw [he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

variable (A : Type u) [CommRing A] [Algebra R A]

local instance : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap R A)))

/-- After scalar extension with a quadratic unit, every value of the
base-changed actual root group is an abstract commutator. -/
theorem mem_commutator_baseChange_incl_of_quadratic_unit
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J)
    (hmu0 : ∑ j, P.root α j * mu j = 0)
    (hmu : ∀ β : J, ∑ j, P.root β j * mu j = 0 →
      P.root β = P.root α ∨ P.root β = -P.root α)
    (hpair : ∑ j, P.root α j * P.coroot α j = 2)
    (tau : Γ(Spec (CommRingCat.of A), ⊤)ˣ)
    (htau : (tau : Γ(Spec (CommRingCat.of A), ⊤)) ^ 2 - 1 = tau)
    (Z : Over (Spec (CommRingCat.of A)))
    (x : Z ⟶ ((GroupScheme.baseChange (algebraBaseMap R A)).obj (Uc i mu (P.coroot α))).X) :
    x ≫ ((GroupScheme.baseChange (algebraBaseMap R A)).map (incl i mu (P.coroot α))).hom.hom ∈
      _root_.commutator (Z ⟶ ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X) := by
  have := hG.smooth
  let t := QuadraticRootCharacterUnit.torusPoint (P.coroot α) (Over.mk (𝟙 _)) tau
  have hu := QuadraticRootCharacterUnit.isUnit_charValue_sub_one
    (P.root α) (P.coroot α) hpair (Over.mk (𝟙 (Spec (CommRingCat.of A)))) tau htau
  have h := mem_commutator_incl_of_unit (splitTorus.baseChangeHom (K := A) G I i) mu t
    (hG.baseChange (algebraBaseMap R A))
    (splitTorus.isFibrewiseMaximalTorus_baseChangeHom I G i hmax)
    hP.baseChange_implicit α hmu0 hmu hu Z
      (x ≫ (rootGroupBaseChangeIso i mu (P.coroot α) A).hom.hom.hom)
  have he := congrArg (fun f => f.hom.hom)
    (rootGroupBaseChangeIso_hom_comp i mu (P.coroot α) A)
  change (rootGroupBaseChangeIso i mu (P.coroot α) A).hom.hom.hom ≫
      (incl (splitTorus.baseChangeHom (K := A) G I i) mu (P.coroot α)).hom.hom =
    ((GroupScheme.baseChange (algebraBaseMap R A)).map
      (incl i mu (P.coroot α))).hom.hom at he
  rw [Category.assoc, he] at h
  exact h

/-- On an affine test, the quadratic fppf refinement makes every actual
root value locally an abstract commutator. -/
theorem locallyCommutator_root_affine_of_pairing
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J)
    (hmu0 : ∑ j, P.root α j * mu j = 0)
    (hmu : ∀ β : J, ∑ j, P.root β j * mu j = 0 →
      P.root β = P.root α ∨ P.root β = -P.root α)
    (hpair : ∑ j, P.root α j * P.coroot α j = 2)
    (Z : Over (Spec (CommRingCat.of R))) [IsAffine Z.left]
    (x : Z ⟶ (Uc i mu (P.coroot α)).X) :
    LocallyCommutator (x ≫ (incl i mu (P.coroot α)).hom.hom) := by
  obtain ⟨W, j, hW, hflat, hsurj, hfp, tau, htau⟩ :=
    QuadraticUnitExtension.exists_unit_test Z
  let : IsAffine W.left := hW
  let : Flat j.left := hflat
  let : Surjective j.left := hsurj
  let : LocallyOfFinitePresentation j.left := hfp
  let A := Γ(W.left, ⊤)
  let ψ : CommRingCat.of R ⟶ Γ(W.left, ⊤) :=
    Spec.preimage (W.left.isoSpec.inv ≫ W.hom)
  let : Algebra R A := ψ.hom.toAlgebra
  let b := algebraBaseMap R A
  let T0 : Over (Spec (CommRingCat.of A)) := Over.mk (𝟙 _)
  let e : W ≅ (Over.map b).obj T0 := Over.isoMk W.left.isoSpec (by
    show W.left.isoSpec.hom ≫ (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ψ.hom)) = W.hom
    rw [Category.id_comp, CommRingCat.ofHom_hom, Spec.map_preimage,
      Iso.hom_inv_id_assoc])
  let tauA : Γ(Spec (CommRingCat.of A), ⊤)ˣ :=
    Units.map e.inv.left.appTop.hom.toMonoidHom tau
  have htauA : (tauA : Γ(Spec (CommRingCat.of A), ⊤)) ^ 2 - 1 = tauA := by
    let φ : Γ(W.left, ⊤) →+* Γ(Spec (CommRingCat.of A), ⊤) :=
      e.inv.left.appTop.hom
    change (φ (tau : Γ(W.left, ⊤))) ^ 2 - 1 = φ (tau : Γ(W.left, ⊤))
    simpa only [map_sub, map_pow, map_one] using
      congrArg φ htau
  let xA := (baseChangePointsEquiv b (Uc i mu (P.coroot α)) T0).symm
    (e.inv ≫ j ≫ x)
  have hA := LocallyCommutator.of_mem
    (mem_commutator_baseChange_incl_of_quadratic_unit i mu A hG hmax hP α
      hmu0 hmu hpair tauA htauA T0 xA)
  have h0 := (locallyCommutator_baseChange_iff b G T0 _).mp hA
  rw [baseChangePointsEquiv_comp] at h0
  dsimp only [xA] at h0
  rw [MulEquiv.apply_symm_apply] at h0
  apply LocallyCommutator.of_surjective j
  have h1 := h0.restrict e.hom
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h1

/-- Affine covers extend the quadratic-refinement argument to every test
scheme. -/
theorem locallyCommutator_root_of_pairing
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J)
    (hmu0 : ∑ j, P.root α j * mu j = 0)
    (hmu : ∀ β : J, ∑ j, P.root β j * mu j = 0 →
      P.root β = P.root α ∨ P.root β = -P.root α)
    (hpair : ∑ j, P.root α j * P.coroot α j = 2)
    (Z : Over (Spec (CommRingCat.of R)))
    (x : Z ⟶ (Uc i mu (P.coroot α)).X) :
    LocallyCommutator (x ≫ (incl i mu (P.coroot α)).hom.hom) := by
  let 𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) Z.left :=
    Z.left.affineCover.changeProp (fun j => by
      have := Z.left.affineCover.map_prop j
      exact ⟨inferInstance, inferInstance⟩)
  apply LocallyCommutator.of_cover 𝒰
  intro j
  let V : Over (Spec (CommRingCat.of R)) := Over.mk (𝒰.f j ≫ Z.hom)
  let a : V ⟶ Z := Over.homMk (𝒰.f j) rfl
  have : IsAffine V.left := inferInstanceAs (IsAffine (Z.left.affineCover.X j))
  exact locallyCommutator_root_affine_of_pairing i mu hG hmax hP α
    hmu0 hmu hpair V (a ≫ x)

/-- Every value of an actual relative root group is fppf-locally in the
abstract commutator subgroup of the original group of points. -/
theorem locallyCommutator_root
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J)
    (hmu0 : ∑ j, P.root α j * mu j = 0)
    (hmu : ∀ β : J, ∑ j, P.root β j * mu j = 0 →
      P.root β = P.root α ∨ P.root β = -P.root α)
    (Z : Over (Spec (CommRingCat.of R)))
    (x : Z ⟶ (Uc i mu (P.coroot α)).X) :
    LocallyCommutator (x ≫ (incl i mu (P.coroot α)).hom.hom) := by
  classical
  cases isEmpty_or_nonempty Z.left with
  | inl h =>
    refine ⟨Scheme.Cover.mkOfCovers PEmpty (fun a => a.elim) (fun a => a.elim)
      (fun z => isEmptyElim z) (fun a => a.elim), fun a => a.elim⟩
  | inr h =>
    let s := Z.hom (Classical.choice h)
    let k := (Spec (CommRingCat.of R)).residueField s
    let : Algebra R k :=
      (Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)).hom.toAlgebra
    have hpair : ∑ j, P.root α j * P.coroot α j = 2 := by
      rw [← hP.pairing k (P.root α) (P.coroot α), P.root_coroot_two]
    exact locallyCommutator_root_of_pairing i mu hG hmax hP α hmu0 hmu hpair Z x

/-- The actual inclusion on root points factors through the subgroup of
fppf-local commutator points. -/
def rootLocallyCommutatorPointHom
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J)
    (hmu0 : ∑ j, P.root α j * mu j = 0)
    (hmu : ∀ β : J, ∑ j, P.root β j * mu j = 0 →
      P.root β = P.root α ∨ P.root β = -P.root α)
    (Z : Over (Spec (CommRingCat.of R))) :
    (Z ⟶ (Uc i mu (P.coroot α)).X) →* locallyCommutatorSubgroup (G := G) Z :=
  (((yonedaGrp.map (incl i mu (P.coroot α))).app (Opposite.op Z)).hom).codRestrict
    (locallyCommutatorSubgroup Z)
    (locallyCommutator_root i mu hG hmax hP α hmu0 hmu Z)

end Langlands.GroupScheme.LocalRootGroup
