import Langlands.GroupScheme.Rational.QuadraticToralFactorization
import Langlands.GroupScheme.AffineWeilUnit
import Langlands.GroupScheme.CocycleBaseChangeTriviality
import Langlands.GroupScheme.CocycleRefinement
import Langlands.Global.AdelicFunctoriality.Norm

/-! # The actual pullback of a quadratic cover at a real place -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField Opposite
open Langlands.AlgebraicGeometry.PointTopology Langlands.Global.AdelicFunctoriality
open scoped NumberField.LiesOver InfiniteExtension TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuadraticToralReduction

set_option backward.isDefEq.respectTransparency false

variable {F L : Type u} [Field F] [Field L] [NumberField F] [NumberField L] [Algebra F L]

omit [NumberField F] [NumberField L] in
theorem upperCompletion_isScalarTower (v : InfinitePlace L) :
    IsScalarTower F L v.Completion :=
  .of_algebraMap_eq fun x => by
    apply InfinitePlace.Completion.ext
    simp [InfinitePlace.Completion.algebraMap_toCompletion,
      UniformSpace.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]

attribute [local instance] upperCompletion_isScalarTower

variable {w : InfinitePlace F} (v : InfinitePlacesAbove L w)

abbrev upperCompletion := v.1.Completion

local notation "K" => w.Completion
local notation "M" => (upperCompletion v)

/-- A quadratic extension has an infinite place above each infinite place. -/
theorem nonempty_infinitePlacesAbove (hdeg : Module.finrank F L = 2) (w : InfinitePlace F) :
    Nonempty (InfinitePlacesAbove L w) := by
  classical
  by_contra h
  let : IsEmpty (InfinitePlacesAbove L w) := not_nonempty_iff.mp h
  have hsum := infiniteLocalDegree_sum (L := L) w
  rw [hdeg, Finset.univ_eq_empty, Finset.sum_empty] at hsum
  exact Nat.zero_ne_add_one _ hsum

omit [NumberField F] in
theorem completion_finrank_of_complex (hw : w.IsReal) (hv : v.1.IsComplex) :
    Module.finrank K M = 2 := by
  have h := w.mult_mul_finrank v.1
  rwa [hw.mult_eq_one, hv.mult_eq_two, one_mul] at h

/-- The completion extension over an inert real place is quadratic Galois. -/
theorem inert_isGalois (hw : w.IsReal) (hv : v.1.IsComplex) : IsGalois K M := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let : Algebra.IsQuadraticExtension K M :=
    { finrank_eq_two' := completion_finrank_of_complex v hw hv }
  infer_instance

private theorem subsingleton_placesAbove_of_complex (hdeg : Module.finrank F L = 2)
    (hw : w.IsReal) (hv : v.1.IsComplex) : Subsingleton (InfinitePlacesAbove L w) := by
  classical
  have hsum := infiniteLocalDegree_sum (L := L) w
  have hdim := completion_finrank_of_complex v hw hv
  have heq (q : InfinitePlacesAbove L w) : q = v := by
    by_contra hq
    have hp : 0 < Module.finrank K q.1.Completion := Module.finrank_pos
    have hle : (∑ i ∈ ({q, v} : Finset (InfinitePlacesAbove L w)),
        Module.finrank K i.1.Completion) ≤ ∑ i : InfinitePlacesAbove L w,
          Module.finrank K i.1.Completion := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    rw [hsum, hdeg, Finset.sum_pair hq, hdim] at hle
    omega
  exact ⟨fun x y => (heq x).trans (heq y).symm⟩

/-- At an inert real place, the completed tensor algebra is its unique upper
completion, with the original coefficient inclusion into it. -/
def inertTensorEquiv (hdeg : Module.finrank F L = 2) (hw : w.IsReal)
    (hv : v.1.IsComplex) : K ⊗[F] L ≃ₐ[K] M := by
  let : Subsingleton (InfinitePlacesAbove L w) := subsingleton_placesAbove_of_complex v hdeg hw hv
  let P (q : InfinitePlacesAbove L w) := q.1.Completion
  let e := Pi.evalAlgHom K P v
  have he : Function.Bijective e := by
    constructor
    · intro x y hxy
      funext i
      have hi : i = v := Subsingleton.elim _ _
      subst i
      exact hxy
    · intro x
      refine ⟨fun i => (Subsingleton.elim v i) ▸ x, ?_⟩
      rfl
  exact (infiniteTensorEquiv (L := L) w).trans (AlgEquiv.ofBijective e he)

@[simp] theorem inertTensorEquiv_one_tmul (hdeg : Module.finrank F L = 2)
    (hw : w.IsReal) (hv : v.1.IsComplex) (x : L) :
    inertTensorEquiv v hdeg hw hv (1 ⊗ₜ[F] x) = algebraMap L M x :=
  infiniteTensorMap_one_tmul w x v

/-- At an inert real place the field cover of the upper completion is
isomorphic to the actual pullback of the original cover. -/
def inertCoverIso (hdeg : Module.finrank F L = 2) (hw : w.IsReal) (hv : v.1.IsComplex) :
    ringTest K M ≅ ringBaseChange F K (ringTest F L) := by
  let e := inertTensorEquiv v hdeg hw hv
  let i : (ringTest K M) ≅ ringTest K (K ⊗[F] L) :=
    { hom := ringTestMap K e.toAlgHom
      inv := ringTestMap K e.symm.toAlgHom
      hom_inv_id := by
        rw [← ringTestMap_comp, show e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id K M
          from AlgHom.ext e.apply_symm_apply, ringTestMap_id]
      inv_hom_id := by
        rw [← ringTestMap_comp, show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id K _
          from AlgHom.ext e.symm_apply_apply, ringTestMap_id] }
  exact i ≪≫ (ringBaseChangeSpectrumIso F K L).symm

/-- The comparison with the inert field cover commutes with the original
inclusion of coefficients. -/
theorem inertCoverIso_over (hdeg : Module.finrank F L = 2) (hw : w.IsReal) (hv : v.1.IsComplex) :
    (Over.map (algebraBaseMap F K)).map (inertCoverIso v hdeg hw hv).hom ≫
        (Over.mapPullbackAdj (algebraBaseMap F K)).counit.app (ringTest F L) =
      (ringTestRestrictScalarsIso F K M).hom ≫ ringTestMap F (IsScalarTower.toAlgHom F L M) := by
  let e := inertTensorEquiv v hdeg hw hv
  have hu := ringPointBaseChangeEquiv_tensorUniversal F K L
  have hfst : (ringBaseChangeSpectrumIso F K L).inv.left ≫
      pullback.fst (ringTest F L).hom (algebraBaseMap F K) =
        (ringTestMap F (Algebra.TensorProduct.includeRight : L →ₐ[F] K ⊗[F] L)).left := by
    rw [← hu, ringPointBaseChangeEquiv_left_fst]
  apply Over.OverMorphism.ext
  change ((ringTestMap K e.toAlgHom).left ≫ (ringBaseChangeSpectrumIso F K L).inv.left) ≫
    pullback.fst (ringTest F L).hom (algebraBaseMap F K) =
      𝟙 _ ≫ (ringTestMap F (IsScalarTower.toAlgHom F L M)).left
  rw [Category.assoc, hfst, Category.id_comp, ringTestMap_left, ringTestMap_left,
    ringTestMap_left, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (inertTensorEquiv_one_tmul v hdeg hw hv)

omit [NumberField F] in
/-- An upper real completion gives a section of the pulled-back cover. -/
theorem split_cover_section (hw : w.IsReal) (hv : v.1.IsReal) :
    Nonempty (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ringBaseChange F K (ringTest F L)) := by
  have hdim : Module.finrank K M = 1 := by
    have h := w.mult_mul_finrank v.1
    rwa [hw.mult_eq_one, hv.mult_eq_one, one_mul] at h
  let e : K ≃ₐ[K] M := AlgEquiv.ofBijective (Algebra.ofId K M)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdim)
  let θ := (e.symm.toAlgHom.restrictScalars F).comp (IsScalarTower.toAlgHom F L M)
  exact ⟨(ringTestSelfIso K).inv ≫ ringPointBaseChangeEquiv F K K (ringTest F L)
    (ringTestMap F θ)⟩

/-- The quadratic coefficient automorphism extends over the actual inert
completion and remains nonidentity there. -/
def inertConjugation (hdeg : Module.finrank F L = 2) (hw : w.IsReal) (hv : v.1.IsComplex)
    (σ : L ≃ₐ[F] L) : M ≃ₐ[K] M := by
  let e := inertTensorEquiv v hdeg hw hv
  let τ := Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[F] K) σ
  let τ' : K ⊗[F] L ≃ₐ[K] K ⊗[F] L :=
    AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun a => by
      change τ (a ⊗ₜ[F] 1) = a ⊗ₜ[F] 1
      simp [τ]
  exact (e.symm.trans τ').trans e

@[simp] theorem inertConjugation_algebraMap (hdeg : Module.finrank F L = 2) (hw : w.IsReal)
    (hv : v.1.IsComplex) (σ : L ≃ₐ[F] L) (x : L) :
    inertConjugation v hdeg hw hv σ (algebraMap L M x) = algebraMap L M (σ x) := by
  rw [← inertTensorEquiv_one_tmul v hdeg hw hv]
  unfold inertConjugation
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  change inertTensorEquiv v hdeg hw hv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[F] K) σ ((1 : K) ⊗ₜ[F] x)) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  exact inertTensorEquiv_one_tmul v hdeg hw hv (σ x)

theorem inertConjugation_ne (hdeg : Module.finrank F L = 2) (hw : w.IsReal) (hv : v.1.IsComplex)
    (σ : L ≃ₐ[F] L) (hσ : σ ≠ 1) : inertConjugation v hdeg hw hv σ ≠ 1 := by
  intro h
  apply hσ
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L M).injective
  have he := inertConjugation_algebraMap v hdeg hw hv σ x
  rw [h] at he
  exact he.symm

/-- Triviality on a cover with a section follows by evaluating the cocycle
along the section over the base. -/
theorem isTrivial_of_cover_section {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}
    (c : Cocycle G U) (s : Over.mk (𝟙 S) ⟶ U) : c.IsTrivial := by
  let q : U ⟶ Over.mk (𝟙 S) := Over.homMk U.hom
  refine ⟨c.toFun (𝟙 U) (q ≫ s), fun {Z} x y => ?_⟩
  have hq : x ≫ q = y ≫ q := Over.OverMorphism.ext ((Over.w x).trans (Over.w y).symm)
  rw [← c.naturality, ← c.naturality]
  simp only [Category.comp_id, ← Category.assoc, hq]
  exact eq_mul_inv_of_mul_eq (c.cocycle x y (y ≫ q ≫ s)).symm

section Restriction

variable {G : GroupScheme (Spec (CommRingCat.of F))}

private abbrev inertProjection : (Over.map (algebraBaseMap F K)).obj (ringTest K M) ⟶ ringTest F L :=
  (ringTestRestrictScalarsIso F K M).hom ≫ ringTestMap F (IsScalarTower.toAlgHom F L M)

/-- Restrict a cocycle to the field cover of the two completions. -/
def inertRestriction (ξ : Cocycle G (ringTest F L)) :
    Cocycle ((baseChange (algebraBaseMap F K)).obj G) (ringTest K M) :=
  ξ.baseChange (algebraBaseMap F K) _ (inertProjection v)

private theorem cocycle_eq_of_toFun_eq
    {S : Scheme.{u}} {Q : GroupScheme S} {U : Over S} {c d : Cocycle Q U}
    (h : ∀ {Z : Over S} (a b : Z ⟶ U), c.toFun a b = d.toFun a b) : c = d := by
  cases c
  cases d
  congr
  funext Z a b
  exact h a b

/-- At an inert real place the restriction to the upper field cover detects
triviality on the full pulled-back cover. -/
theorem isTrivial_inertRestriction_iff (ξ : Cocycle G (ringTest F L))
    (hdeg : Module.finrank F L = 2) (hw : w.IsReal) (hv : v.1.IsComplex) :
    (inertRestriction v ξ).IsTrivial ↔ (ξ.baseChangePullback (algebraBaseMap F K)).IsTrivial := by
  let b := algebraBaseMap F K
  let e := inertCoverIso v hdeg hw hv
  let ζ := ξ.baseChangePullback b
  have hres : ζ.refine e.hom = inertRestriction v ξ := by
    apply cocycle_eq_of_toFun_eq
    intro Z a c
    apply (baseChangePointsEquiv b G Z).injective
    simp only [Cocycle.refine_toFun, ζ, Cocycle.baseChangePullback, Cocycle.baseChange_toFun,
      inertRestriction, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [inertCoverIso_over]
    change _ = baseChangePointsEquiv b G Z ((ξ.baseChange b _ (inertProjection v)).toFun a c)
    rw [Cocycle.baseChange_toFun]
  rw [← hres]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨e.inv ≫ g, fun a c => ?_⟩
    have h := hg (a ≫ e.inv) (c ≫ e.inv)
    simpa only [Cocycle.refine_toFun, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
  · exact fun h => h.refine e.hom

/-- The primary Galois value of the local restriction is the scalar extension
of the original value. -/
theorem inertRestriction_value (ξ : Cocycle G (ringTest F L))
    (hdeg : Module.finrank F L = 2) (hw : w.IsReal) (hv : v.1.IsComplex) (σ : L ≃ₐ[F] L) :
    (affinePointsBaseChangeMulEquiv F K M G).symm
      (GaloisCocycle.value (inertRestriction v ξ) (inertConjugation v hdeg hw hv σ)) =
        ringTestMap F (IsScalarTower.toAlgHom F L M) ≫ GaloisCocycle.value ξ σ := by
  let b := algebraBaseMap F K
  let τ := inertConjugation v hdeg hw hv σ
  let r := inertProjection v
  have hσr : (Over.map b).map (GaloisCocycle.arrow K M τ) ≫ r =
      r ≫ GaloisCocycle.arrow F L σ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap L M))) =
      (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap L M))) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom)
    simp only [Category.id_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (inertConjugation_algebraMap v hdeg hw hv σ)
  change (ringTestRestrictScalarsIso F K M).inv ≫ baseChangePointsEquiv b G _
      ((ξ.baseChange b _ r).toFun (𝟙 _) (GaloisCocycle.arrow K M τ)) = _
  rw [Cocycle.baseChange_toFun, CategoryTheory.Functor.map_id, hσr]
  simp only [Category.id_comp]
  have h := ξ.naturality r (𝟙 (ringTest F L)) (GaloisCocycle.arrow F L σ)
  simp only [Category.comp_id] at h
  rw [h]
  change (ringTestRestrictScalarsIso F K M).inv ≫
      ((ringTestRestrictScalarsIso F K M).hom ≫ ringTestMap F (IsScalarTower.toAlgHom F L M)) ≫
        GaloisCocycle.value ξ σ = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]

end Restriction

end Langlands.GroupScheme.QuadraticToralReduction
