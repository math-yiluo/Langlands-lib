import Langlands.Representation.Aubert.LocalFieldGradedGrothendieck
import Langlands.Representation.Aubert.LocalFieldSupportSign

/-! Aubert's support sign as an automorphism of the graded induction product. -/

open scoped DirectSum

namespace Langlands.Aubert.LocalFieldGraded

universe uF uV

/-- The support-sign twist is involutive, commutes with the graded product,
fixes the unit, and gives the adjustment of a homogeneous operator by
precomposition. -/
def LocalFieldSupportSignLawsStatement : Prop :=
  ∀ (K : AllFieldBZ.LocalFieldPackage.{uF}) (T : K.TopologicalData)
    (h : LocalFieldBinaryProductExactLengthStatement.{uF, uV}),
    letI := T.topology
    let H n := GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier
    let sign n : H n →ₗ[ℤ] H n := adjustOperator T n LinearMap.id
    let S := DirectSum.toModule ℤ ℕ (GradedGrothendieckGroup.{uF, uV} T)
      (fun n => (inclusion T n).comp (sign n))
    (∀ n (D : H n →ₗ[ℤ] H n), adjustOperator T n D = D.comp (sign n)) ∧
    (∀ n (x : H n), sign n (sign n x) = x) ∧
    (∀ x y, S (multiplication T h x y) = multiplication T h (S x) (S y)) ∧
    S (unit T) = unit T

end Langlands.Aubert.LocalFieldGraded
