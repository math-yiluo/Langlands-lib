# Common epsilon tests for actual supercuspidal families

Author: Worker 357.

This internal correspondence adapter defines
`Langlands.Correspondence.CommonSupercuspidalEpsilonFactors` and its comparison
API. All classes, characters, measures and factor certificates are the actual
published correspondence objects. The field, parameter-carrier and
representation-carrier universes remain independent.

The relation says that two `SupercuspidalMap` families, evaluated on the same
Weil class of rank `k + 2` and the same Weil class of rank `r + 1`, possess a
common JPSS epsilon certificate whenever `r ≤ k`. It asserts existence of one
coefficient and exponent witnessing both factor relations; missing factors do
not agree vacuously.

The provenance is the uniqueness induction in Henniart 2000, Section 1.4,
printed page 441 (PDF page 3) of the registered original
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The comparison relation is a derived internal interface isolating the precise
input consumed by that argument. It does not assert existence of a
correspondence or prove the local converse theorem.

`isSupercuspidalPairEpsilonFactor_iff_class` identifies the symmetric
correspondence factor relation with `RankinSelberg.IsClassEpsilonFactor` when
the first class has at least the second class's rank. Its proof uses quotient
induction and the published candidate-first convention on representatives.

`IsArithmeticPairEpsilonFactor.unique` compares two certificates using one
fixed reciprocity family and one fixed local-constant system. The existence
clauses provide admissible continuous bottom-field data and a geometric
Frobenius. The universal clauses then identify both monomials at every complex
spectral parameter. The published injectivity of real spectral points and
`unitMonomial_eq_of_infinite` identify the coefficient and exponent.

`commonSupercuspidalEpsilonFactors_of_pairFactors` extracts the epsilon
certificates from two supplied separate pair-factor compatibility predicates
for the same system. Arithmetic uniqueness identifies their values. It needs a
specified character and a specified self-dual measure.

`supercuspidalMap_eq_of_commonEpsilonFactors` retains the published
`SupercuspidalLocalConverseStatement` as an explicit hypothesis. Strong
induction on the positive rank starts with equality of the rank-one functions.
At rank `k + 2`, surjectivity of the first family lifts each actual
supercuspidal test of rank `r + 1`, for `r ≤ k`, to a Weil class. The induction
hypothesis identifies the two lower-rank images. The common epsilon
certificate therefore gives the hypothesis of local converse for all
supercuspidal tests, and local converse identifies the candidate images.
Function extensionality gives equality of the whole families.

`supercuspidalMap_eq_of_pairFactors` combines the arithmetic comparison with
the rank induction. It consumes the existing pair-factor compatibility
predicates for a single fixed system, with rank-one agreement, surjectivity,
local converse, the actual character and its self-dual measure still supplied.

The module proves no unconditional correspondence statement. Rank-one equality,
rankwise surjectivity, an actual character and self-dual measure, and local
converse remain explicit inputs. Arithmetic uniqueness here does not compare
different systems or reciprocity families; those comparisons are separate
obligations for the existential systems in the full correspondence predicate.

The complete module compiled in the project Lean service with no errors or
warnings. Inspection of `CommonSupercuspidalEpsilonFactors` confirmed that it
returns `Prop`, retains universe parameters `uF`, `uP`, `uA`, and uses only
`propext`, `Classical.choice` and `Quot.sound`. This development check supplies
no independent acceptance or unconditional correspondence proof.
