import Langlands.Representation.CuspidalSupport.LeviGrothendieckTransport
import Langlands.AllField.Representation.Induction.Parabolic

/-! Weyl invariance of exact induced classes for actual local-field GL. -/

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GeneralLinear SmoothRep CuspidalSupport

universe u v

/-- Weyl conjugation of an actual standard matrix Levi and its inducing
representation preserves the class of normalized induction in exact K₀. -/
def LocalFieldMatrixInducedWeylStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F) (n : ℕ)
    (B C : BlockShape n) (w : Equiv.Perm (Fin n)) (hw : ConjugatesLevi (F := F) B C w),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (A : SmoothRep.{0, u, max (u + 1) v} ℂ (B.Levi F)), A.HasFiniteLength →
      let I := (T.normalizedParabolicInductionFunctor B).obj A
      let A' := (transportFunctor B C w hw).obj A
      let J := (T.normalizedParabolicInductionFunctor C).obj A'
      ∃ (hI : I.HasFiniteLength) (hJ : J.HasFiniteLength),
        FiniteLengthGrothendieckGroup.ofRepresentation I hI =
          FiniteLengthGrothendieckGroup.ofRepresentation J hJ

end Langlands.Aubert.General.RationalPointFamily.GL
