import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor

/-!
# Finite length and exactness of the actual product-Levi refinement functors

Proposition definitions asserting that the existing normalized induction and
normalized Jacquet functors attached to an ordered refinement of a product Levi
of `GL_n` preserve finite group-algebra length and actual short exact sequences
of finite-length smooth representations. Every rank, outer block shape and
refinement is included, with independent field and input-carrier universes.
Nothing here proves these assertions.
-/

namespace Langlands.Parabolic

universe uF uV

open CategoryTheory

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For every rank `n`, outer block shape `B` and refinement `S`, normalized
refined induction sends each smooth representation of the actual refined Levi
with carrier in `Type uV` and finite group-algebra length to a representation of
the product Levi `B.Levi F.Carrier`, with carrier in `Type (max uF uV)`, of
finite group-algebra length. This is a proposition definition, not its proof. -/
def NormalizedRefinedInductionFiniteLengthStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B),
    SmoothRep.PreservesFiniteLength (T.normalizedRefinedInductionFunctor.{uF, uV} B S)

/-- For every rank `n`, outer block shape `B` and refinement `S`, the normalized
refined Jacquet functor sends each smooth representation of `B.Levi F.Carrier`
with carrier in `Type uV` and finite group-algebra length to a representation of
the actual refined Levi, with carrier in `Type uV`, of finite group-algebra
length. This is a proposition definition, not its proof. -/
def NormalizedRefinedJacquetFiniteLengthStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B),
    SmoothRep.PreservesFiniteLength (T.normalizedRefinedJacquetFunctor.{uF, uV} B S)

/-- For every rank `n`, outer block shape `B` and refinement `S`, normalized
refined induction sends each actual short exact sequence of finite-length smooth
refined-Levi representations, read on the underlying intertwiners, to an actual
short exact sequence of product-Levi representations. This is a proposition
definition, not its proof. -/
def NormalizedRefinedInductionShortExactStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B),
    SmoothRep.PreservesFiniteLengthShortExact
      (T.normalizedRefinedInductionFunctor.{uF, uV} B S)

/-- For every rank `n`, outer block shape `B` and refinement `S`, the normalized
refined Jacquet functor sends each actual short exact sequence of finite-length
smooth product-Levi representations, read on the underlying intertwiners, to an
actual short exact sequence of refined-Levi representations. This is a
proposition definition, not its proof. -/
def NormalizedRefinedJacquetShortExactStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B),
    SmoothRep.PreservesFiniteLengthShortExact
      (T.normalizedRefinedJacquetFunctor.{uF, uV} B S)

/-- Both actual refinement functors preserve finite group-algebra length and
short exact sequences of finite-length objects, for the fixed field and
topological data and every rank, outer shape and refinement. -/
def NormalizedRefinedFiniteLengthExactnessStatement : Prop :=
  NormalizedRefinedInductionFiniteLengthStatement.{uF, uV} F T ∧
    NormalizedRefinedJacquetFiniteLengthStatement.{uF, uV} F T ∧
      NormalizedRefinedInductionShortExactStatement.{uF, uV} F T ∧
        NormalizedRefinedJacquetShortExactStatement.{uF, uV} F T

/-! ### The saturated carrier universe

At `uV := max uF uV` the induction output universe `max uF (max uF uV)`
normalizes to `max uF uV`, so both refinement functors act between the
saturated carrier categories, and the four clauses are the published
preservation predicates for these saturated functors. -/

noncomputable example (n : ℕ) (B : GeneralLinear.BlockShape n)
    (S : Geometric.BlockRefinement B) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (Geometric.refinedLevi F.Carrier B S) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier) :=
  T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S

noncomputable example (n : ℕ) (B : GeneralLinear.BlockShape n)
    (S : Geometric.BlockRefinement B) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (Geometric.refinedLevi F.Carrier B S) :=
  T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S

example (h : NormalizedRefinedInductionFiniteLengthStatement.{uF, max uF uV} F T)
    (n : ℕ) (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    SmoothRep.PreservesFiniteLength (T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S) :=
  h n B S

example (h : NormalizedRefinedJacquetFiniteLengthStatement.{uF, max uF uV} F T)
    (n : ℕ) (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    SmoothRep.PreservesFiniteLength (T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S) :=
  h n B S

example (h : NormalizedRefinedInductionShortExactStatement.{uF, max uF uV} F T)
    (n : ℕ) (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    SmoothRep.PreservesFiniteLengthShortExact
      (T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S) :=
  h n B S

example (h : NormalizedRefinedJacquetShortExactStatement.{uF, max uF uV} F T)
    (n : ℕ) (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    SmoothRep.PreservesFiniteLengthShortExact
      (T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S) :=
  h n B S

/- The conjunction supplies all four saturated predicates, in the stated order. -/
example (h : NormalizedRefinedFiniteLengthExactnessStatement.{uF, max uF uV} F T)
    (n : ℕ) (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    SmoothRep.PreservesFiniteLength (T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S) ∧
      SmoothRep.PreservesFiniteLength (T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S) ∧
      SmoothRep.PreservesFiniteLengthShortExact
        (T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S) ∧
      SmoothRep.PreservesFiniteLengthShortExact
        (T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S) :=
  ⟨h.1 n B S, h.2.1 n B S, h.2.2.1 n B S, h.2.2.2 n B S⟩

/-! ### Unfolded clauses

At any carrier universe the clauses apply to individual actual objects and
morphisms; no premise beyond finite length and short exactness is needed. -/

example (h : NormalizedRefinedInductionFiniteLengthStatement.{uF, uV} F T)
    (n : ℕ) (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (Geometric.refinedLevi F.Carrier B S),
      A.HasFiniteLength →
        ((T.normalizedRefinedInductionFunctor.{uF, uV} B S).obj A).HasFiniteLength :=
  h n B S

example (h : NormalizedRefinedJacquetShortExactStatement.{uF, uV} F T)
    (n : ℕ) (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    ∀ ⦃A D E : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)⦄ (f : A ⟶ D) (g : D ⟶ E),
      A.HasFiniteLength → D.HasFiniteLength → E.HasFiniteLength →
        SmoothRep.IsShortExact (SmoothRep.hom f) (SmoothRep.hom g) →
          SmoothRep.IsShortExact
            (SmoothRep.hom ((T.normalizedRefinedJacquetFunctor.{uF, uV} B S).map f))
            (SmoothRep.hom ((T.normalizedRefinedJacquetFunctor.{uF, uV} B S).map g)) :=
  h n B S

end Langlands.Parabolic
