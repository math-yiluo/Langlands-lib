import Langlands.Representation.Aubert.LocalFieldGradedAdjustedOperator

/-! Involutivity of the actual support-adjusted graded Aubert operator. -/

namespace Langlands.Aubert.LocalFieldGraded

open General.RationalPointFamily.GL
open AllFieldBZ (LocalFieldPackage)

universe u v

/-- The support-adjusted Aubert operator on the whole graded exact
Grothendieck group squares to the identity. -/
def LocalFieldGradedAdjustedInvolutivityStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F),
    letI : TopologicalSpace (LocalFieldPackage.ofField F).Carrier := T.topology
    ∃ h : ∀ n, LocalFieldMatrixParabolicExactLength.{u, v} T n,
      let d := gradedAdjustedOperator.{u, v} T h
      d.comp d = LinearMap.id

end Langlands.Aubert.LocalFieldGraded
