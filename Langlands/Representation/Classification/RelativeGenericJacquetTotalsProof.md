# Equal actual Jacquet totals for generic fine cuspidal induction

Authors: Worker 982 and Worker 166.

`Langlands.glRelativeGenericJacquetTotals` proves
`Langlands.GLRelativeGenericJacquetTotalsStatement.{uF, uV}`, with independent
universes for the p-adic field and the fine carrier. Fix a positive rank `n`,
a block shape `B` with refinement `S` and flattened shape `C`, an irreducible
cuspidal unitarizable representation `ω` of the fine Levi, an arbitrary fine
real parameter `v₀`, and a coarse real parameter `t` that is relatively generic.
Let `σ` be the real twist of `ω` by `-v₀` plus the restriction of `t`, let `τ` be
the corresponding fine twist, `I` the actual full inner induction of `τ`, and
`N` the number of permutations associating `σ` with itself on `C`. The theorem
gives actual finite composition series of both the inner and the ambient full
opposite-Jacquet modules of `I` in which `τ` has multiplicity exactly `N`.

## Inputs

The proof uses two published unconditional count theorems, each specialized to
the field universe `uF` and both carrier universes equal to `uV`:

- `productLeviCuspidalJacquetMultiplicity`
  (`ProductLeviCuspidalJacquetMultiplicityStatement`, product-Levi task
  `74173499-0d59-4f2e-96b3-4fba98114d42`);
- `glCuspidalJacquetMultiplicityPrerequisites`
  (`GLCuspidalJacquetMultiplicityPrerequisitesStatement`, which is by definition
  `GLCuspidalJacquetMultiplicityStatement`; GL task
  `c9dbd607-82e5-4821-b367-736e876565d9`).

No count, filtration or other certificate is assumed.

## Inner clause

A real twist of the irreducible `ω` is irreducible
(`isIrreducible_leviRealPowerTwist_iff`), and fine-twist regularity
(`fineTwistIrreducibleAdmissible`) shows that `σ` is cuspidal. The product-Levi
count then gives the inner opposite-Jacquet module a finite series in which `τ`
has multiplicity equal to the number of associating permutations in the coarse
block Weyl group. Relative genericity (`glRelativeGenericWeylCount`) identifies
this restricted cardinality with the full self-association cardinality `N`.

## Ambient clause

Normalized induction transitivity (`normalizedRefinementInductionTransitivity`)
and the composed/flattened induction comparison (`composedFlattenedInduction`)
give an actual equivalence from the outer induction of `I` to the standard
normalized induction of `σ` from `C`; the fine transport followed by its inverse
cancels. The imported
`Langlands.RelativeJacquetFiltrationMultiplicityProof.composedOppositeJacquetCongr`
descends this equivalence and its inverse through the actual composed
opposite-Jacquet maps to an equivalence of the quotients. Pulling
back along `flattenedLeviEquiv` and applying the normalized flattened-opposite
comparison (`flattenedOppositeJacquetComparison`) identifies the ambient module
with the standard opposite Jacquet module of the induction of `σ`. The GL count,
applied with both Levis equal to `C` and the trivial association, gives that
standard module a finite series in which `σ` has multiplicity `N`. Published
multiplicity transport, first along representation equivalences and then along
the group isomorphism `flattenedLeviEquiv`, moves this series back to the
original ambient module and the fine twist `τ`.

## Provenance

The proof body is Worker 166's development assembly
`glRelativeGenericJacquetTotals_of_counts`. In that assembly the two count
statements were explicit premises. Here they are replaced by the published
theorems above, and the identical quotient-equivalence helper is reused directly
from `Classification.RelativeJacquetFiltrationMultiplicityProof`. Extracting a
representation equivalence from the natural induction isomorphism follows the
published pattern in `CuspidalSupport.RefinedCuspidalInductionReduction`.
