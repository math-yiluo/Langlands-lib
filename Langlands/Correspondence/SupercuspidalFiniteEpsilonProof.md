# Finite selection and lifting of actual epsilon tests

Worker 357 proves the existing
`Langlands.Henniart.FiniteSupercuspidalEpsilonLiftingStatement F` in
`finiteSupercuspidalEpsilonLifting`. The same module gives finite separation
conditional on the published local converse proposition, and applies it to
the published bounded-level strata with their stated finiteness premise.
The statement modules and their imports are unchanged.

## Proof of finite lifting

The supplied `lower` maps act on actual continuous irreducible local Weil
classes at each lower rank, and their surjectivity is a hypothesis of the
existing target. `FiniteEpsilon.project_surjective` takes a test consisting
of a rank index and a supercuspidal class, chooses a preimage under the map
at that index, and retains the index. Thus projection of the dependent sum
is surjective without identifying any of the carrier universes.

Apply the published `finiteTestLifting` to the finite test family `D` and
this projection. It returns a finite family `S`, containment of its image
in `D`, and coverage of every member of `D`. Those two conclusions are
exactly `FiniteEpsilon.ExactImage`. For two candidates agreeing at the
images of every selected lift, coverage supplies that agreement at every
test in `D`. The given `Separates` hypothesis then proves equality.
`liftedSeparates_of_exactImage` implements this last step.

The theorem retains every hypothesis of the target. Self-duality is not
needed by the finite selection argument itself; it remains in the theorem
through the unchanged proposition definition. No finiteness of the
candidate set is needed here. Empty test families are handled by the
generic finite lifting theorem without an inhabitedness assumption.

## Conditional finite separation

`finiteSupercuspidalEpsilonSeparation_of_localConverse` takes
`RankinSelberg.SupercuspidalLocalConverseStatement` as an explicit premise.
For two unequal candidates, if every lower-rank test satisfied `Agree`,
the very same common epsilon witnesses would establish
`SameClassEpsilonFactors`. Local converse, at the supplied self-dual
measure, would contradict their inequality. Classical logic therefore
gives a test at which `Agree` fails.

Give the finite candidate subtype its finite type structure. On the finite
type of ordered pairs with unequal entries, choose one such failed test.
The image of this choice is the finite separating family, chosen before
the comparison of any candidate pair. Agreement on the whole family
contradicts the chosen failed test of an unequal pair. Empty and singleton
candidate sets require no test. The argument treats `Agree` as its published
common-certificate relation throughout. It needs no new factor-existence
or uniqueness assumption because the supplied local converse premise
already consumes this relation.

`supercuspidalStratumEpsilonSeparation_of_finiteSeparation` specializes
finite separation to the published fixed-central-character, bounded-first-level
stratum, using the exact bounded-level finiteness proposition already
present as a premise in the stratum target. The final
`supercuspidalFiniteEpsilon_of_localConverse` combines these reductions
and finite lifting at every prime and p-adic field.

## Provenance and scope

The source of the finite-selection and lifting argument is Henniart,
*Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
p-adique* (2000), Section 4.3, printed pp.452–453, retained PDF pages 14–15.
Registered source: `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
These original pages were read. They select a distinguishing test for each
unequal candidate pair and lift the finitely many tests using lower-rank
surjectivity. The present proof implements that finite argument on the
existing actual local class spaces.

Candidate rank is `k + 2`; tests indexed by `r : Fin (k + 1)` have rank
`r.val + 1`, including ranks one and `k + 1`. Field, candidate, test and
Weil carrier universes remain independent. The common certificate is an
entire epsilon monomial at one fixed additive character and Haar measure,
in the existing candidate-first order.

Henniart's additional finite-order twist normalization and construction of
the lower-rank surjections are outside this proof. It does not establish
local converse, bounded-level finiteness, arithmetic epsilon comparison,
global choice independence, or the closed all-field correspondence target.
Only finite lifting is proved without an additional proposition premise;
the separation and combined results explicitly retain local converse.

## Verification

The complete module compiled in the prepared Lean service without errors
or warnings. Inspection of `finiteSupercuspidalEpsilonLifting` reports a
theorem with independent universe parameters `uF`, `uC`, `uT`, `uW` and
only `propext`, `Classical.choice`, and `Quot.sound` as axioms. The theorem
returns the existing `FiniteSupercuspidalEpsilonLiftingStatement F` without
an additional hypothesis. These development checks do not replace exact
target validation, independent review, or publication.
