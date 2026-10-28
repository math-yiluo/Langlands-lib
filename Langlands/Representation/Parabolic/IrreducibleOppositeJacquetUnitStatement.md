# Irreducible opposite-Jacquet unit embeddings: statement

Author: Worker 166.

`Langlands.Parabolic.IrreducibleOppositeJacquetUnitStatement.{uF,uV}` is
the conjunction of two existence propositions. The field universe `uF` and
the inducing-carrier universe `uV` are independent. Both clauses quantify over
every prime, compatible `PadicField` and `TopologicalData`, positive rank and
block shape.

`StandardIrreducibleOppositeJacquetUnitClause` takes any irreducible admissible
complex representation `σ` of the block Levi. With
`I = Rep.of (T.normalizedParabolicInduced B σ.ρ)`, it asserts the existence of
an actual intertwining map

\[
  j:\sigma\longrightarrow r_{\overline P}(I)
\]

whose underlying function is injective. The target is exactly the existing
`CuspidalJacquetMultiplicity.oppositeJacquet T B I`.

`RefinedIrreducibleOppositeJacquetUnitClause` additionally quantifies over every
actual block refinement `S`. It allows an arbitrary irreducible admissible
representation of the whole refined Levi, without a tensor-product restriction.
Here `I = Rep.of (T.normalizedRefinedInduced B S σ.ρ)` is a representation of the
whole product Levi, and the target is exactly
`T.normalizedRefinedOppositeJacquet B S I.ρ`. Both induced carriers have universe
`max uF uV`. There are no cuspidality, finite-length, unitarity, splitting,
genericity or central-character assumptions.

These are internal derived statements. Their provenance is the published
`Langlands.Parabolic.normalizedSecondAdjointness` together with preservation of
admissibility by actual normalized induction and its nonvanishing. Choose a
second-adjointness equivalence for the relevant parabolic, and take its ambient
input to be `I`. Induction is admissible, and compact local sections realize any
prescribed value at the identity, so an irreducible nonzero inducing carrier
gives a nonzero induced carrier. The nonzero identity of `I` therefore maps
under the linear equivalence to a nonzero intertwiner `σ → r_op(I)`.
An intertwiner from an irreducible representation is either injective or zero,
which gives the asserted embedding. The refined nonvanishing result is already
available as `normalizedRefinedInductionNonvanishing`; the same compact-section
argument applies to the standard induction. A separate proof module will
implement this derivation.

The word “unit” describes this second-adjointness origin. The proposition
asserts existence only; it selects no canonical embedding and states no
naturality. It proves no multiplicity comparison, quotient-detection result or
irreducible-head consequence.
