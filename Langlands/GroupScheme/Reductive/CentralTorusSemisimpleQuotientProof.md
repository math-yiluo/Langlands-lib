# A central torus with semisimple quotient in every connected reductive group

Author: Worker 1282.

`Langlands.GroupScheme.reductiveCentralTorusSemisimpleQuotient` proves exactly
the published proposition
`Langlands.GroupScheme.ReductiveCentralTorusSemisimpleQuotientStatement.{u}`
at every universe `u`.

For every field `k : Type u` and every connected reductive group scheme `G`
over `Spec k`, it constructs a commutative group scheme `Z` and a morphism
`j : Z.toGrp ⟶ G`. The structure morphism of `Z` is affine and locally of
finite type, `Z` is a torus, and `j` is a closed central subgroup inclusion.
For every affine, locally finite type group scheme `Q` and morphism
`q : G ⟶ Q` satisfying
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q`, the conclusion is
`IsSemisimple Q`: connected reductivity together with a finite full
scheme-theoretic centre. The quotient predicate retains equality of the
kernel and subgroup-functor range on every test scheme. The theorem applies
over imperfect fields and in every characteristic.

## Implemented proof

The Lean proof applies
`reductiveCentralTorusSemisimpleQuotient_of_structure` from
[`CentralTorusSemisimpleQuotientReduction`](CentralTorusSemisimpleQuotientReduction.md)
to three published unconditional theorems, all at the same universe `u`:

- `solvableRadicalExistence`, from
  [`SolvableRadicalExistenceProof`](../Rational/SolvableRadicalExistenceProof.md),
  constructs an actual ground-field solvable radical of every smooth
  connected affine field group.
- `algClosedReductiveNormalSolvableTorus`, from
  [`AlgClosedNormalSolvableTorusProof`](../Rational/AlgClosedNormalSolvableTorusProof.md),
  makes every smooth connected solvable normal closed subgroup of a
  pseudo-reductive group over an algebraically closed field a central torus.
- `reductiveLargestCentralSubtorusBaseChange`, from
  [`LargestCentralSubtorusBaseChangeProof`](../Rational/LargestCentralSubtorusBaseChangeProof.md),
  preserves the largest-central-subtorus property under arbitrary field
  extension.

The imported reduction first constructs a ground-field solvable radical
`r : R ⟶ G`. Over the algebraic closure, the normal-solvable-subgroup theorem
makes its base change a central torus. Torus structure and centrality descend
to `k`. Greatestness of the ground-field radical then makes it a largest
central subtorus. Compatibility of largest central subtori with field
extension gives greatestness against all smooth connected solvable normal
closed subgroups over the algebraic closure. Thus `r` is an actual geometric
solvable radical.

The reduction equips `R` with its torus commutativity to obtain `Z`, keeping
the same underlying group scheme and inclusion. Closedness in affine `G`
gives affineness of `Z`, and smoothness gives local finite type.

For every quotient in the target, the quotient helper proves connected
reductivity over `k` and triviality of the solvable radical over the
algebraic closure. Every smooth connected central closed subgroup there is
commutative, hence solvable and normal, so its range is trivial. The
finite-centre helper deduces finiteness of the full scheme-theoretic centre,
including its nilpotents. The resulting semisimplicity descends from the
algebraic closure to `k`.

All three structural premises of the reduction are discharged by the
imported proofs. The resulting theorem has exactly the unchanged target as
its type. As in that target, semisimplicity is asserted for every quotient
satisfying its hypotheses; existence of a quotient is not a separate
conclusion.

## Provenance

This is an internal composition of published proofs. The supporting
reduction was contributed by Workers 1282 and 1616. The three structural
proofs and their own prerequisites are documented in the linked Markdown
files. The original-source derivation of the target is recorded in
[`CentralTorusSemisimpleQuotientStatement`](CentralTorusSemisimpleQuotientStatement.md).
This final composition introduces no additional structural assertion or
source citation.
