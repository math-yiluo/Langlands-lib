import Langlands.Automorphic.GroupSchemeNormOneSmooth
import Langlands.Global.AdelicCentralPositiveHeightProof
import Langlands.Global.AdelicSplitCenterQuotient

/-! # Infinite and finite product coordinates on the norm-one adelic group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)

private theorem ofInfinite_infinite_of_finite_eq_one (x : AdelicGroupPoints F G)
    (hx : finite F G x = 1) : ofInfinite F G (infinite F G x) = x := by
  rw [ofInfinite_eq_pair, ← hx, pair_projections]

/-- Removing the positive central factor leaves the finite projection unchanged. -/
@[simp] theorem finite_normOneProjection (x : AdelicGroupPoints F G) :
    finite F G (normOneProjection F G T i hi I e hc x) = finite F G x := by
  have hT : IsSplitTorus T.toGrp := ⟨I, inferInstance, ⟨e⟩⟩
  simp only [normOneProjection_apply, normOneFactor_val, map_mul, map_inv,
    RepresentationGrowth.finite_positivePointMap F T i hT, inv_one, one_mul]

private theorem ofInfinite_infinite_projection (a : InfiniteAdelicGroupPoints F G) :
    ofInfinite F G (infinite F G (normOneProjection F G T i hi I e hc (ofInfinite F G a))) =
      (normOneProjection F G T i hi I e hc (ofInfinite F G a)).val := by
  apply ofInfinite_infinite_of_finite_eq_one
  rw [finite_normOneProjection, finite_ofInfinite]

private theorem infinite_projection_mem (a : InfiniteAdelicGroupPoints F G) :
    infinite F G (normOneProjection F G T i hi I e hc (ofInfinite F G a)) ∈
      infiniteNormOneSubgroup F G := by
  let p := normOneProjection F G T i hi I e hc
  change ofInfinite F G (infinite F G (p (ofInfinite F G a))) ∈ normOneSubgroup F G
  rw [ofInfinite_infinite_projection]
  exact (p (ofInfinite F G a)).property

include T i hi I e hc in
/-- The norm-one projection on pure infinite points takes values in the infinite norm-one
subgroup. -/
def infiniteNormOneProjection :
    InfiniteAdelicGroupPoints F G →ₜ* infiniteNormOneSubgroup F G := by
  let p := normOneProjection F G T i hi I e hc
  let coeNormOne : normOneSubgroup F G →ₜ* AdelicGroupPoints F G :=
    ⟨(normOneSubgroup F G).subtype, continuous_subtype_val⟩
  let pInf := (infinite F G).comp (coeNormOne.comp (p.comp (ofInfinite F G)))
  have hmem (a : InfiniteAdelicGroupPoints F G) : pInf a ∈ infiniteNormOneSubgroup F G :=
    infinite_projection_mem F G T i hi I e hc a
  exact ⟨pInf.toMonoidHom.codRestrict (infiniteNormOneSubgroup F G) hmem,
    pInf.continuous.subtype_mk hmem⟩

@[simp] theorem infiniteNormOneInclusion_projection (a : InfiniteAdelicGroupPoints F G) :
    infiniteNormOneInclusion F G (infiniteNormOneProjection F G T i hi I e hc a) =
      normOneProjection F G T i hi I e hc (ofInfinite F G a) :=
  Subtype.ext (ofInfinite_infinite_projection F G T i hi I e hc a)

@[simp] theorem infiniteNormOneProjection_normOne (a : infiniteNormOneSubgroup F G) :
    infiniteNormOneProjection F G T i hi I e hc a = a := by
  let p := normOneProjection F G T i hi I e hc
  apply Subtype.ext
  change infinite F G (p ((infiniteNormOneInclusion F G a).val)) = a.val
  rw [normOneProjection_normOne]
  exact infinite_ofInfinite F G a

private theorem infiniteNormOneProjection_positive (a : intrinsicSubgroup F T) :
    infiniteNormOneProjection F G T i hi I e hc (infinite F G (positivePointMap F G T i a)) = 1 := by
  let p := normOneProjection F G T i hi I e hc
  have hT : IsSplitTorus T.toGrp := ⟨I, inferInstance, ⟨e⟩⟩
  apply Subtype.ext
  change infinite F G (p (ofInfinite F G (infinite F G (positivePointMap F G T i a)))) = 1
  rw [ofInfinite_infinite_of_finite_eq_one F G _
    (RepresentationGrowth.finite_positivePointMap F T i hT a),
    normOneProjection_positivePointMap, Subgroup.coe_one, map_one]

section

set_option maxRecDepth 1024

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
include T i hi I e hc in
/-- The norm-one group is the product of its pure infinite subgroup and the unmodified
finite adelic point group. The finite section is the norm-one projection of pure finite
points. -/
def normOneProduct :
    infiniteNormOneSubgroup F G × FiniteAdelicGroupPoints F G ≃ₜ* normOneSubgroup F G := by
  let p := normOneProjection F G T i hi I e hc
  let q := infiniteNormOneProjection F G T i hi I e hc
  let forward : infiniteNormOneSubgroup F G × FiniteAdelicGroupPoints F G →
      normOneSubgroup F G := fun x => p (pair F G x.1 x.2)
  let inverse : normOneSubgroup F G →
      infiniteNormOneSubgroup F G × FiniteAdelicGroupPoints F G :=
    fun x => (q (infinite F G x), finite F G x)
  have left_inv : Function.LeftInverse inverse forward := by
    intro x
    apply Prod.ext
    · change q (infinite F G (p (pair F G x.1 x.2))) = x.1
      simp only [p, q, normOneProjection_apply, normOneFactor_val, map_mul, map_inv,
        infiniteNormOneProjection_positive F G T i hi I e hc, inv_one, one_mul,
        infinite_pair, infiniteNormOneProjection_normOne F G T i hi I e hc]
    · change finite F G (p (pair F G x.1 x.2)) = x.2
      simp only [p, finite_normOneProjection, finite_pair]
  have right_inv : Function.RightInverse inverse forward := by
    intro x
    change p (pair F G (q (infinite F G x)) (finite F G x)) = x
    have hpair (a : InfiniteAdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G) :
        pair F G a b = ofInfinite F G a * ofFinite F G b := by
      rw [ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, mul_one, one_mul]
    rw [hpair, map_mul p]
    change p ((infiniteNormOneInclusion F G (q (infinite F G x))).val) *
      p (ofFinite F G (finite F G x)) = x
    dsimp only [p, q]
    rw [normOneProjection_normOne, infiniteNormOneInclusion_projection, ← map_mul,
      ← hpair, pair_projections, normOneProjection_normOne]
  have hmul (x y : infiniteNormOneSubgroup F G × FiniteAdelicGroupPoints F G) :
      forward (x * y) = forward x * forward y := by
    change p (pair F G (x.1.val * y.1.val) (x.2 * y.2)) =
      p (pair F G x.1 x.2) * p (pair F G y.1 y.2)
    rw [← pair_mul, map_mul]
  have hforward : Continuous forward := by
    have hcoords : Continuous (fun x : infiniteNormOneSubgroup F G ×
        FiniteAdelicGroupPoints F G => (x.1.val, x.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hpaired : Continuous ((fun x : InfiniteAdelicGroupPoints F G ×
        FiniteAdelicGroupPoints F G => pair F G x.1 x.2) ∘
        fun x : infiniteNormOneSubgroup F G × FiniteAdelicGroupPoints F G =>
          (x.1.val, x.2)) :=
      (continuous_pair F G).comp hcoords
    exact p.continuous.comp hpaired
  have hinverse : Continuous inverse := by
    have hcoe : Continuous (fun x : normOneSubgroup F G => x.val) := continuous_subtype_val
    have hInf : Continuous (((infinite F G) : AdelicGroupPoints F G →
        InfiniteAdelicGroupPoints F G) ∘ fun x : normOneSubgroup F G => x.val) :=
      (infinite F G).continuous.comp hcoe
    have hFin : Continuous (((finite F G) : AdelicGroupPoints F G →
        FiniteAdelicGroupPoints F G) ∘ fun x : normOneSubgroup F G => x.val) :=
      (finite F G).continuous.comp hcoe
    exact (q.continuous.comp hInf).prodMk hFin
  exact ⟨⟨⟨forward, inverse, left_inv, right_inv⟩, hmul⟩, hforward, hinverse⟩

@[simp] theorem normOneProduct_apply (a : infiniteNormOneSubgroup F G)
    (b : FiniteAdelicGroupPoints F G) :
    normOneProduct F G T i hi I e hc (a, b) =
      normOneProjection F G T i hi I e hc (pair F G a b) := rfl

@[simp] theorem normOneProduct_symm_apply (x : normOneSubgroup F G) :
    (normOneProduct F G T i hi I e hc).symm x =
      (infiniteNormOneProjection F G T i hi I e hc (infinite F G x), finite F G x) := rfl

@[simp] theorem normOneProduct_infinite (a : infiniteNormOneSubgroup F G) :
    normOneProduct F G T i hi I e hc (a, 1) = infiniteNormOneInclusion F G a := by
  rw [normOneProduct_apply, ← ofInfinite_eq_pair]
  exact normOneProjection_normOne F G T i hi I e hc (infiniteNormOneInclusion F G a)

@[simp] theorem normOneProduct_finite (b : FiniteAdelicGroupPoints F G) :
    normOneProduct F G T i hi I e hc (1, b) =
      normOneProjection F G T i hi I e hc (ofFinite F G b) := by
  rw [normOneProduct_apply, Subgroup.coe_one, ← ofFinite_eq_pair]

end

end Langlands.Automorphic.GroupSchemeFunctions
