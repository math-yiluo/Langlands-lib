# Central stable vector subgroups of split unipotent groups

Worker 1405 and Worker 1389.

The theorem `Langlands.GroupScheme.RelativeRoot.splitUnipotentStableVectorSubgroup.{u}`
proves the unchanged proposition
`Langlands.GroupScheme.RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u}`
(module `Langlands.GroupScheme.Rational.SplitUnipotentStableVectorStatement`).
It holds over every field k in universe u, of any characteristic, finite or
infinite, perfect or not. The acting group H is any smooth affine group over
k, connected or not. The theorem has no premise.

## Proof

The proof is one application:

- `splitUnipotentStableVectorSubgroup_of_perfectFieldUnipotentSplit`, from
  `Langlands.GroupScheme.Rational.SplitUnipotentStableVectorReduction`, derives
  the target from `Langlands.GroupScheme.PerfectFieldUnipotentSplitStatement.{u}`.
- The published theorem `Langlands.GroupScheme.perfectFieldUnipotentSplit.{u}`
  (module `Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof`) proves that
  statement.

## Modules of this proof

The paired Markdown of each module describes its proofs.

- `Langlands.Algebra.PolynomialCocycle.Homogeneous` and
  `Langlands.Algebra.PolynomialCocycle.Coboundary` (Worker 1389): under the
  torsion condition, a symmetric polynomial 2-cocycle is a polynomial
  coboundary (`exists_coboundary`).
- `Langlands.GroupScheme.Rational.SplitCommutativeVector` (Worker 1389): a
  commutative affine split unipotent group whose points are all killed by
  `ringChar k` is a vector group (`isVectorGroup_of_isSplitUnipotent_of_exponent`).
- `Langlands.GroupScheme.Rational.SplitSeriesProductDecomposition`: for one
  step K ⟶ H ⟶ V of a split series, H is isomorphic to K ⊗ V as a scheme.
- `Langlands.GroupScheme.Rational.SplitUnipotentRationalDensity` and
  `Langlands.GroupScheme.Rational.SplitUnipotentRationalDetection`: over an
  infinite field, rational points of split unipotent groups are dense, and
  morphisms out of such groups are detected on rational fibres.
- `Langlands.GroupScheme.Rational.SplitUnipotentCommutativeEnvelope`: over an
  infinite field, a family of homomorphisms from a split group into a
  commutative group factors through a split closed subgroup.
- `Langlands.GroupScheme.Rational.SplitUnipotentStableCenter`: a nontrivial
  split stable central subgroup killed by `ringChar k`, over infinite fields
  and over fields where all smooth connected unipotent groups are split. Its
  last theorem gives the target for such fields from the vector group step.
- `Langlands.GroupScheme.Rational.SplitUnipotentStableVectorReduction`: puts
  the cases together. Infinite fields use the density argument. Finite fields
  are perfect, so the hypothesis makes all their smooth connected unipotent
  groups split.

Only the axioms `propext`, `Classical.choice` and `Quot.sound` are used.

## Literature

The target statement's Markdown gives its sources in Conrad, Gabber and
Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), Appendix B. The formal
proof does not follow that route. It does not use the cckp-kernel or
Theorem B.2.5. Over infinite fields it uses the density of rational points,
a route worked out for this formalization. Over finite fields it uses the
published `perfectFieldUnipotentSplit`, whose Markdown cites J. S. Milne,
*Algebraic Groups* (2017), Corollary 16.24.
