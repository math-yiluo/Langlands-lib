# The cuspidal-induction Jacquet constituent Weyl piece

Authors: Workers 1091 and 264.

`Langlands.glCuspidalInductionJacquetConstituent.{uF,uV,uW}` proves exactly
the published proposition
`Langlands.GLCuspidalInductionJacquetConstituentStatement.{uF,uV,uW}`
(module `Langlands.Representation.Exponents.WeylBranchPiecesStatement`).
The field universe `uF`, the universe `uV` of the inducing cuspidal
representation `ω` and the universe `uW` of the cuspidal constituent `ρ`
remain independent.

## Statement

For every prime `p`, every actual `F : PadicField p` with compatible
topological data `T`, every positive rank `n`, shape `D` and refinements
`R R'` of `D`, let `ω` be an irreducible Levi-cuspidal representation of
`(D.flatten R).Levi F` and `ρ` an irreducible Levi-cuspidal representation of
`(D.flatten R').Levi F`. If `ρ` is an actual subquotient
(`WeylBranchPieces.IsSubquotient`) of the pull-back along
`flattenedLeviEquiv F D R'` of the inner opposite Jacquet module
`RelativeJacquetMultiplicity.innerJacquet T D R'` of the inner normalized
induction `RelativeJacquetMultiplicity.innerInduced T D R` of `ω` (pulled back
along the inverse of `flattenedLeviEquiv F D R`), then there are
`h ∈ Geometric.blockWeyl D`, a witness
`hh : CuspidalSupport.ConjugatesLevi (D.flatten R) (D.flatten R') h` and an
actual representation equivalence
`ρ.ρ.Equiv (CuspidalSupport.transport (D.flatten R) (D.flatten R') h hh ω.ρ)`.
The theorem has no further premise.

## Proof

The proof is one application:

```
glCuspidalInductionJacquetConstituent_of_cuspidalPiece
  glInducedOppositeJacquetCuspidalPiece.{uF, uW, uV}
```

* `Langlands.glCuspidalInductionJacquetConstituent_of_cuspidalPiece`
  (Library module
  `Langlands.Representation.Exponents.CuspidalInductionJacquetConstituentConditional`,
  Worker 1091) derives the target at `.{uF,uV,uW}` from
  `GLInducedOppositeJacquetCuspidalPieceStatement.{uF,uW,uV}`. It factors `ω`
  and `ρ` as external tensor products over the blocks of `D`, identifies the
  inner opposite Jacquet module of the inner induction with the external
  tensor product of the blockwise opposite Jacquet modules of the blockwise
  inductions, and obtains each factor of `ρ` as an actual subquotient of the
  matching factor. For each block, the general-linear cuspidal-piece
  statement gives a refinement, a permutation and a transported
  subrepresentation of an upper refined Jacquet module of the factor of `ω`.
  Cuspidality of that factor makes every proper refined Jacquet module zero,
  so only the full refinement remains. Its piece is the transport of the
  factor of `ω`, which is irreducible, so the factor of `ρ` is equivalent to
  it. The blockwise permutations assemble into `h = blockPermOf D σ` in
  `blockWeyl D`. The paired Markdown of that module describes every step.
* `Langlands.glInducedOppositeJacquetCuspidalPiece`
  (Library module
  `Langlands.Representation.Geometric.InducedOppositeCuspidalPieceProof`,
  Workers 164 and 954) proves
  `GLInducedOppositeJacquetCuspidalPieceStatement` unconditionally, from the
  published GL_n geometric lemma `Geometric.padicGeometricLemma` and
  proper-induction vanishing `CuspidalSupport.padicProperRefinedInduction`.

Universes: in the hypothesis of the conditional theorem, the inducing
representation consists of the factors of `ω` (universe `uV`) and the cuspidal
quotient consists of the factors of `ρ` (universe `uW`). The cuspidal-piece
statement has levels `uF uV uW` in the order field, cuspidal target, inducing
representation, so it is instantiated at `.{uF, uW, uV}`.

Thus the Weyl element and the equivalence come from actual filtrations: the
geometric lemma's filtration of the opposite Jacquet module of each block
induction, located by the subquotient argument in the cuspidal-piece proof.
No filtration, branch or geometric-lemma certificate is a premise. The proof
does not use `GLRelativeRegularComparisonStatement` or a theorem relying on
it, the full reflection theorem, Langlands parameter or data uniqueness,
square-integrable classification, or Silberger 1978 Lemma 5.3 / Corollary 5.4:
the two applied theorems are unconditional Library theorems. Neither they nor
the declarations they use take those results as hypotheses or prove them.
The axioms are `propext`, `Classical.choice` and `Quot.sound`.

The parallel conditional route
`Langlands.glCuspidalInductionJacquetConstituent_of_localization` (module
`Exponents/CuspidalInductionJacquetConstituentReduction`, Worker 264), from
`GLProductLeviCuspidalLocalizationStatement`, is not used here.

## Provenance

The target is an internal derived statement: the product-Levi form, for
opposite Jacquet modules, of the cuspidal case of the normalized geometric
lemma of Bernstein and Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), registered as `bernstein-zelevinsky-1977-induced-i`:
Theorem 2.12 (printed p.448) combined with section 2.4(d) (printed p.447), as
used in Corollary 2.13. No source states it in this form, and the implemented
route (tensor factorization over the blocks of `D`, then the general-linear
cuspidal-piece extraction per block) is not the source's argument.
