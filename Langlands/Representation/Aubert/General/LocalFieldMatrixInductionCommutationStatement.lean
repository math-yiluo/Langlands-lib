import Langlands.Representation.Aubert.General.LocalFieldGLRationalOperatorStatement
import Langlands.Representation.Aubert.RefinedAlternatingConstruction
import Langlands.AllField.Representation.Geometric.RefinementFunctorsSupplement

/-! The actual matrix Aubert operator commutes with normalized induction. -/

noncomputable section

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GeneralLinear Geometric SmoothRep

universe u v

variable {F : Type u} [Field F] (T : LocalFieldData F) {n : ℕ} (B : BlockShape n)

/-- The exactness and finite-length witnesses for the two normalized functors
of every standard refinement inside `B`. -/
def LocalFieldMatrixRefinementExactLength : Prop :=
  letI := T.topology
  ∀ S : BlockRefinement B,
    let i := T.normalizedRefinedInductionFunctor.{u, max (u + 1) v} B S
    let r := T.normalizedRefinedJacquetFunctor.{u, max (u + 1) v} B S
    PreservesFiniteLength i ∧ PreservesFiniteLengthShortExact i ∧
      PreservesFiniteLength r ∧ PreservesFiniteLengthShortExact r

/-- The literal signed sum of exact induction–Jacquet endomorphisms on
the Grothendieck group of a standard product Levi. -/
def localFieldMatrixRefinedAlternatingOperator
    (h : LocalFieldMatrixRefinementExactLength.{u, v} T B) :
    letI := T.topology
    B.FiniteLengthGrothendieckGroup.{max (u + 1) v, u} F →ₗ[ℤ]
      B.FiniteLengthGrothendieckGroup.{max (u + 1) v, u} F := by
  letI := T.topology
  letI : Fintype (BlockRefinement B) := Fintype.ofFinite _
  exact ∑ S : BlockRefinement B, ((-1 : ℤ) ^ refinementSignExponent B S) •
    (FiniteLengthGrothendieckGroup.map (T.normalizedRefinedInductionFunctor B S)
      (h S).1 (h S).2.1).comp
      (FiniteLengthGrothendieckGroup.map (T.normalizedRefinedJacquetFunctor B S)
        (h S).2.2.1 (h S).2.2.2)

/-- For every field and rank, the actual normalized induction map intertwines
the two unadjusted operators on the full exact Grothendieck groups. -/
def LocalFieldMatrixInductionCommutationStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∃ (h : LocalFieldMatrixParabolicExactLength.{u, v} T n)
      (hR : LocalFieldMatrixRefinementExactLength.{u, v} T B),
      let i := FiniteLengthGrothendieckGroup.map (T.normalizedParabolicInductionFunctor B)
        (h B).1 (h B).2.1
      (localFieldMatrixAlternatingOperator T n h).comp i =
        i.comp (localFieldMatrixRefinedAlternatingOperator T B hR)

end Langlands.Aubert.General.RationalPointFamily.GL
