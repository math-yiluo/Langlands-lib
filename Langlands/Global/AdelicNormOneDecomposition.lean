import Langlands.Global.AdelicLogSection

/-! # Actual positive-torus and norm-one adelic factorization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (i : T.toGrp ⟶ G)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- Recover the actual intrinsic positive-torus coordinate from the ambient logarithm. -/
def positiveFactor : AdelicGroupPoints F G →ₜ* intrinsicSubgroup F T where
  toMonoidHom := (positiveAmbientLogEquiv F G T i hi I e).symm.toMulEquiv.toMonoidHom.comp
    (characterLogHom F G).toMonoidHom
  continuous_toFun := (positiveAmbientLogEquiv F G T i hi I e).symm.continuous.comp
    (characterLogHom F G).continuous

@[simp] theorem positiveFactor_apply (x : AdelicGroupPoints F G) :
    positiveFactor F G T i hi I e x =
      (positiveAmbientLogEquiv F G T i hi I e).symm (characterLogHom F G x) := rfl

@[simp] theorem positiveFactor_positivePointMap (a : intrinsicSubgroup F T) :
    positiveFactor F G T i hi I e (positivePointMap F G T i a) = a := by
  rw [positiveFactor_apply, characterLogHom_positivePointMap F G T i hi I e,
    ContinuousMulEquiv.symm_apply_apply]

@[simp] theorem positiveFactor_normOne (n : normOneSubgroup F G) :
    positiveFactor F G T i hi I e (n : AdelicGroupPoints F G) = 1 := by
  have hn : characterLogHom F G (n : AdelicGroupPoints F G) = 1 :=
    (characterLog_eq_zero_iff F G _).mpr n.property
  rw [positiveFactor_apply, hn, map_one]

/-- Remove the actual positive point image to obtain an actual norm-one point. -/
def normOneFactor (x : AdelicGroupPoints F G) : normOneSubgroup F G :=
  ⟨(positivePointMap F G T i (positiveFactor F G T i hi I e x))⁻¹ * x, by
    apply (characterLog_eq_zero_iff F G _).mp
    change characterLogHom F G
      ((positivePointMap F G T i (positiveFactor F G T i hi I e x))⁻¹ * x) = 1
    rw [map_mul, map_inv, characterLogHom_positivePointMap F G T i hi I e,
      positiveFactor_apply, ContinuousMulEquiv.apply_symm_apply, inv_mul_cancel]⟩

@[simp] theorem normOneFactor_val (x : AdelicGroupPoints F G) :
    (normOneFactor F G T i hi I e x : AdelicGroupPoints F G) =
      (positivePointMap F G T i (positiveFactor F G T i hi I e x))⁻¹ * x := rfl

theorem positiveFactor_mul_normOne (a : intrinsicSubgroup F T) (n : normOneSubgroup F G) :
    positiveFactor F G T i hi I e (positivePointMap F G T i a * n) = a := by
  rw [map_mul, positiveFactor_positivePointMap, positiveFactor_normOne, mul_one]

theorem positivePointMap_mul_normOneFactor (x : AdelicGroupPoints F G) :
    positivePointMap F G T i (positiveFactor F G T i hi I e x) *
      (normOneFactor F G T i hi I e x : AdelicGroupPoints F G) = x :=
  mul_inv_cancel_left _ _

/-- Multiplication gives a genuine equivalence of actual adelic point carriers. -/
def normOneDecompositionEquiv :
    intrinsicSubgroup F T × normOneSubgroup F G ≃ AdelicGroupPoints F G where
  toFun p := positivePointMap F G T i p.1 * p.2
  invFun x := (positiveFactor F G T i hi I e x, normOneFactor F G T i hi I e x)
  left_inv p := by
    apply Prod.ext
    · exact positiveFactor_mul_normOne F G T i hi I e p.1 p.2
    · apply Subtype.ext
      change (positivePointMap F G T i
        (positiveFactor F G T i hi I e (positivePointMap F G T i p.1 * p.2)))⁻¹ *
          (positivePointMap F G T i p.1 * p.2) = p.2
      rw [positiveFactor_mul_normOne, inv_mul_cancel_left]
  right_inv := positivePointMap_mul_normOneFactor F G T i hi I e

@[simp] theorem normOneDecompositionEquiv_apply
    (p : intrinsicSubgroup F T × normOneSubgroup F G) :
    normOneDecompositionEquiv F G T i hi I e p = positivePointMap F G T i p.1 * p.2 := rfl

omit [(characterRestrict i).range.FiniteIndex] in
/-- The actual scheme-theoretic centrality condition implies commutation on adelic points. -/
theorem positivePointMap_commute (hc : IsCentral i) (a : intrinsicSubgroup F T)
    (x : AdelicGroupPoints F G) : Commute (positivePointMap F G T i a) x :=
  commute_of_mem_center (hc _ a.val) x

variable [IsAffine G.X.left]

theorem continuous_normOneFactor : Continuous (normOneFactor F G T i hi I e) :=
  (((positivePointMap F G T i).continuous.comp
    (positiveFactor F G T i hi I e).continuous).inv.mul continuous_id).subtype_mk _

/-- Multiplication is a homeomorphism from intrinsic positive points times actual norm-one
points to the actual ambient adelic group. Centrality is not needed for this assertion. -/
def normOneDecomposition :
    intrinsicSubgroup F T × normOneSubgroup F G ≃ₜ AdelicGroupPoints F G where
  toEquiv := normOneDecompositionEquiv F G T i hi I e
  continuous_toFun := ((positivePointMap F G T i).continuous.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (positiveFactor F G T i hi I e).continuous.prodMk
    (continuous_normOneFactor F G T i hi I e)

@[simp] theorem normOneDecomposition_apply
    (p : intrinsicSubgroup F T × normOneSubgroup F G) :
    normOneDecomposition F G T i hi I e p = positivePointMap F G T i p.1 * p.2 := rfl

@[simp] theorem normOneDecomposition_symm_apply (x : AdelicGroupPoints F G) :
    (normOneDecomposition F G T i hi I e).symm x =
      (positiveFactor F G T i hi I e x, normOneFactor F G T i hi I e x) := rfl

/-- Actual centrality upgrades the multiplication homeomorphism to a topological group
equivalence with the ordinary direct product group. -/
def normOneDecompositionMulEquiv (hc : IsCentral i) :
    intrinsicSubgroup F T × normOneSubgroup F G ≃ₜ* AdelicGroupPoints F G where
  toHomeomorph := normOneDecomposition F G T i hi I e
  map_mul' p q := by
    change positivePointMap F G T i (p.1 * q.1) *
      ((p.2 : AdelicGroupPoints F G) * q.2) =
        (positivePointMap F G T i p.1 * p.2) * (positivePointMap F G T i q.1 * q.2)
    rw [map_mul]
    have h : Commute (positivePointMap F G T i q.1) (p.2 : AdelicGroupPoints F G) :=
      positivePointMap_commute F G T i hc q.1 p.2
    exact h.mul_mul_mul_comm (positivePointMap F G T i p.1) (q.2 : AdelicGroupPoints F G)

@[simp] theorem normOneDecompositionMulEquiv_apply (hc : IsCentral i)
    (p : intrinsicSubgroup F T × normOneSubgroup F G) :
    normOneDecompositionMulEquiv F G T i hi I e hc p =
      positivePointMap F G T i p.1 * p.2 := rfl

end Langlands.Global.PositiveRealTorus
