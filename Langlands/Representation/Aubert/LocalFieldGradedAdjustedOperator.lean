import Langlands.Representation.Aubert.General.LocalFieldGLRationalOperatorStatement
import Langlands.Representation.Aubert.LocalFieldGradedGrothendieck
import Langlands.Representation.Aubert.LocalFieldSupportSign

/-! The support-adjusted alternating induction–Jacquet operator in all ranks. -/

noncomputable section

namespace Langlands.Aubert.LocalFieldGraded

open General.RationalPointFamily.GL
open AllFieldBZ (LocalFieldPackage)

universe uF uV

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The sum of the rankwise support-adjusted actual alternating operators. -/
def gradedAdjustedOperator (h : ∀ n, LocalFieldMatrixParabolicExactLength.{uF, uV} T n) :
    GradedGrothendieckGroup.{uF, max (uF + 1) uV} (K := LocalFieldPackage.ofField F) T →ₗ[ℤ]
      GradedGrothendieckGroup.{uF, max (uF + 1) uV} (K := LocalFieldPackage.ofField F) T :=
  letI : TopologicalSpace (LocalFieldPackage.ofField F).Carrier := T.topology
  DirectSum.lmap fun n => adjustOperator.{uF, max (uF + 1) uV}
    (K := LocalFieldPackage.ofField F) T n (localFieldMatrixAlternatingOperator T n (h n))

@[simp]
theorem gradedAdjustedOperator_homogeneous
    (h : ∀ n, LocalFieldMatrixParabolicExactLength.{uF, uV} T n) (n : ℕ) :
    letI := T.topology
    ∀ x : GeneralLinear.FiniteLengthGrothendieckGroup.{max (uF + 1) uV, uF} n F,
      gradedAdjustedOperator T h
          (inclusion.{uF, max (uF + 1) uV} (K := LocalFieldPackage.ofField F) T n x) =
        inclusion.{uF, max (uF + 1) uV} (K := LocalFieldPackage.ofField F) T n
          (adjustOperator.{uF, max (uF + 1) uV} (K := LocalFieldPackage.ofField F) T n
            (localFieldMatrixAlternatingOperator T n (h n)) x) := by
  let : TopologicalSpace (LocalFieldPackage.ofField F).Carrier := T.topology
  intro x
  let W := fun k => GeneralLinear.FiniteLengthGrothendieckGroup.{max (uF + 1) uV, uF}
    k (LocalFieldPackage.ofField F).Carrier
  let f : ∀ k, W k →ₗ[ℤ] W k := fun k =>
    adjustOperator.{uF, max (uF + 1) uV} (K := LocalFieldPackage.ofField F) T k
      (localFieldMatrixAlternatingOperator T k (h k))
  exact DirectSum.lmap_lof (M := W) (N := W) f n x

end Langlands.Aubert.LocalFieldGraded
