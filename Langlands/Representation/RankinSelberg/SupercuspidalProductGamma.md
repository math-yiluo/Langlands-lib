# Common gamma factors against products of supercuspidals

This internal supporting module assembles previously proved reductions. The
supercuspidal Kirillov statement remains an explicit premise. It does not
prove the local converse theorem.

`IsPadicPairEpsilonFactor.gammaFactor_of_supercuspidal` treats an irreducible
supercuspidal representation of `GL_(r+1)` against a smooth representation of
`GL_(n+1)`, where `n < r`. From an epsilon certificate `e = (c,m)` it obtains
the actual p-adic gamma certificate for the rational monomial `c X^m`. The
Kirillov statement is required only at the larger carrier universe. Its support
clause gives mirabolic tests; `SupercuspidalZeroBlockLaurent` then proves
Laurent-valuedness of every existing block-zero rational continuation. The
previous reduction applies this to both the original and inverse-transpose
pairs and preserves all blocks and quotient-measure quantifiers.

`isOfWhittakerType_of_supercuspidalKirillov` uses the existence clause in the
Kirillov statement to obtain a nonzero standard Whittaker functional. Together
with irreducibility and the admissibility included in supercuspidality, this
gives genericity. The published p-adic multiplicity-one theorem, through
`isOfWhittakerType_of_isGeneric`, then gives full Whittaker type.

`SameProductGammaFactors F ψ ν k π π'` concerns larger representations of
`GL_(k+2)` with carriers in `uV`. It quantifies over any finite ordered family
of supercuspidal representations with carriers in `uW` and ranks `m i+1` whose
sum is `k+1`. For each family it requires one rational function that is the
gamma factor of both larger representations against the actual canonical
normalized induction of that family to `GL_(k+1)`. It uses the existing
`IsPadicPairGammaFactor` relation, retaining all its existence, functional,
measure and block conditions.

`SameSupercuspidalEpsilonFactors.productGammaFactors` proves this predicate
for irreducible supercuspidal larger representations and a self-dual additive
Haar measure, under the supercuspidal Kirillov statement at both carrier
universes `uV` and `uW`. Each block rank is at most the total rank `k+1`, so
the common-epsilon premise supplies a common epsilon certificate for that
block. The first lemma converts it to a common gamma certificate. Published
`gammaMultiplicativity` supplies gamma factors for both induced pairs, and
uniqueness identifies their individual factors with the common monomials.
Their finite products therefore agree. The two rank orders coincide here
because every test and induced rank is strictly smaller than `k+2`.

The field universe `uF` and the two carrier universes are independent. The
induced representation has the existing induced carrier universe
`max uF uW`; no resizing or classification theorem is assumed. The provenance
is this composition of Library APIs and the block-zero Laurent helper. The
Kirillov proof and the final converse argument remain separate obligations.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
