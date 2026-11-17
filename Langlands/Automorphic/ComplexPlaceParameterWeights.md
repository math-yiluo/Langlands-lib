# Complex-place exponent coordinates and highest weights

This internal vocabulary translates the published actual polar character data
into Clozel's exponent convention. It defines matching relations and elementary
invariance under permutations. It supplies no comparison theorem between actual
automorphic parameters and infinitesimal characters.

For signed weight `m` and complex exponent `t`, the published
`ComplexCharacterData.character_eq` reads
`χ(z) = (z/|z|)^m |z|^(2t)`, with Euclidean norm. Writing `z = r u` gives
`u^m r^(2t)`. In the notation `z^a conjugate(z)^b` this is
`u^(a-b) r^(a+b)`, so `a-b=m`, `a+b=2t` and hence
`a=t+m/2`, `b=t-m/2`. The notation denotes this single-valued polar character:
the angular exponent is an integer. It does not denote a product of arbitrary
principal-branch complex powers. The helpers `zExponent` and `zBarExponent`
use the signed integer `weight`; the absolute value used by the L-factor is
irrelevant here.

For the upper triangular Borel, the zero-indexed half-sum of positive roots is
`rho n i = ((n : ℂ)-1)/2 - (i.val : ℂ)`. Subtraction is in `ℂ`, including
`n-1`. `MatchesHighestWeight n ds μz μzBar` requires length `n` and two
independent list permutations from the exponent lists to `μz+rho` and
`μzBar+rho`. At a complex place the Weyl group is `S_n × S_n`; an infinitesimal
character retains the two separate Weyl orbits, not their pairing into blocks.

`IsClozelRegularAlgebraic n ds` requires length `n`, both exponents of each
block in the coset `(n-1)/2 + ℤ`, and no repetition in either exponent list.
It imposes no purity, unitarity or paired-order condition.

`MatchesGlobalHighestWeight F n ds μ` uses the existing subtype of actual
complex places and `ArchimedeanGL.EmbeddingIndex F`. At each complex place `v`,
the z weight is `μ (.inr (v,false))` and the conjugate-z weight is
`μ (.inr (v,true))`. This is the orientation proved by the published
`embeddingComponent_inr_false` and `embeddingComponent_inr_true`.
`MatchesInfinitesimalCharacter F n ds χ` requires some such `μ` whose existing
`IsHighestWeightCharacter F n μ χ` holds for the actual algebra character
`χ : EnvelopingCenter F n →ₐ[ℂ] ℂ`.

The target `ArchimedeanGL.IsRegularAlgebraicCharacter` uses an unshifted,
integral, antitone highest weight. Thus the shift occurs in the parameter
matching relation, not in that target. Both global definitions retain the
number-field universe `uF`. Real embedding weights remain unrestricted by
complex-place matching. When real places occur, complex coordinates cannot
determine the whole global character. Later full determination and a global
regular-algebraic equivalence therefore require `NumberField.IsTotallyComplex F`.
Neither result is asserted here.

The four named `*_iff_of_perm` theorems preserve local matching, local Clozel
regularity, global highest-weight matching and infinitesimal-character matching.
Their proofs use preservation of length and membership under a list permutation,
map the permutation to each exponent list, and transport its permutation or
no-repetition property. The global proofs apply the local result at every actual
complex place; the last proof keeps the same highest-weight witness and center
character. These are elementary internal proofs. They make no assertion about
permutation invariance of the actual literal standard-module embedding predicate.

The paired module `ComplexPlaceParameterWeightsExamples` supplies the requested
compiled calculations using actual `Langlands.Archimedean.characterOfParams`
data and checks the embedding orientation.

| Rank and blocks `(m,t)` | z exponents | Conjugate-z exponents | Unshifted highest weights at z and conjugate z |
| --- | --- | --- | --- |
| One: `(3,1/2)` | `(2)` | `(-1)` | `(2)`, `(-1)` |
| Two: `(0,1/2)`, `(0,-1/2)` | `(1/2,-1/2)` | `(1/2,-1/2)` | `(0,0)`, `(0,0)` |
| Two: `(1,2)`, `(1,-1)` | `(5/2,-1/2)` | `(3/2,-3/2)` | `(2,0)`, `(1,-1)` |

The half-sums are `(0)` and `(1/2,-1/2)`, respectively. Every displayed
list satisfies the Clozel predicate: both exponent lists have distinct entries
and the required common coset. Two trivial character blocks instead have
repeated coordinates `(0,0)` in both lists and fail the predicate. These
calculations do not assert a standard-module embedding for any automorphic class.

## Source correspondence

L. Clozel, *Motifs et formes automorphes: applications du principe de
fonctorialité*, in *Automorphic Forms, Shimura Varieties, and L-functions*,
Vol. I (1990), registered source
`clozel-milne-automorphic-forms-shimura-varieties-l-functions-i-1990`:
Définition 1.8 and the following remark, printed pp.89–90 (PDF100–101), give
the exponent coset and separate Weyl orbits. Définition 3.12, printed p.111
(PDF122), gives regularity. The proof of Théorème 3.13, printed pp.112–113
(PDF123–124), explains subtraction of the half-sum to obtain dominant integral
highest weights and comparison modulo the complex Weyl group. All five scanned
pages were visually read. No source-specific erratum was found in the Library.

The explicit list predicates and their permutation lemmas are internal
translations of these conventions, not additional results attributed to Clozel.
The polar convention is reused from `ArchimedeanAttachment`; the precise global
highest-weight and center-character targets are reused from `RegularAlgebraic`.
No Harish-Chandra isomorphism is assumed or constructed.
