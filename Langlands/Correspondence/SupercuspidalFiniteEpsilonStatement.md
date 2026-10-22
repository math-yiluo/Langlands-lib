# Finite epsilon tests on actual supercuspidal classes

Author: Worker 78. This module supplies proposition definitions; it does not
prove the stated separation and lifting results.

The module defines the proposition
`Langlands.Henniart.SupercuspidalFiniteEpsilonStatement`, with three
components: finite separation of actual supercuspidal classes, its
fixed-central-character bounded-first-level application, and finite lifting
through supplied surjections from actual irreducible local Weil classes.

## Sources and provenance

Henniart, *Caractérisation de la correspondance de Langlands locale par les
facteurs ε de paires* (1993), Section 1.1 and Corollary, printed pp.339–340,
and Theorem 4.1, printed p.348, are the principal sources. Registered source:
`henniart-1993-epsilon-pairs`, SHA256
`057967169237036da64c0e5a72c69e8ddfd69176bebade0ef13588de24809763`.
The corollary distinguishes supercuspidals of rank at least two using all
supercuspidal tests of ranks 1 through one less than the candidate rank.
It has no additional equal-central-character hypothesis. Theorem 4.1 uses
surjections from irreducible Weil classes at each lower rank, not an LLC
bijection.

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
un corps p-adique* (2000), Sections 4.1–4.4, printed pp.452–453,
especially Section 4.3, selects finitely many tests for a finite candidate
set and lifts them through lower-rank surjections. Registered source:
`henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
Sections 2.5–2.8, printed pp.445–448, concern the global-generated lattices;
they do not alone supply local finiteness or every lower-rank surjection.
Both originals were read, including rendered pp.340 and 348 of the 1993
paper and p.452 of the 2000 paper. The rendered pages confirm the endpoint
ranks where OCR inequalities are unreliable.

The present propositions are an internal finite-selection reformulation,
not a transcription of a single displayed source theorem. For a finite
candidate set, choose a distinguishing test for each distinct pair and
collect these tests into a finite set. Choose a preimage of each selected
test under the surjection at its rank. Both choices precede comparison of
any candidate pair. The elementary targets
`Langlands.Henniart.FiniteSeparationStatement`, `FiniteTestLiftingStatement`
and `FiniteLiftedSeparationStatement` describe the generic finite arguments;
they are not duplicated or asserted proved here. Applying their
function-valued formulation to this relation additionally uses factor
existence and uniqueness.

## Objects, ranks, and normalization

The field is an actual `PadicField p` with its canonical topology and local
field data. Candidate classes use
`PadicField.SupercuspidalClass F (k + 2)`. Thus every rank at least two is
covered without a rank-zero case or transport along arithmetic equalities.
`FiniteEpsilon.SupercuspidalTest F k` is the dependent sum over
`r : Fin (k + 1)` of supercuspidal classes of rank `r.val + 1`. These are
exactly all ranks from 1 through `k + 1`, below the candidate rank `k + 2`.
At candidate rank two the sole allowed test rank is one.

`FiniteEpsilon.WeilTest` uses
`Weil.Local.LocalContinuousIrreducibleWeilClasses F (r.val + 1)`, attached to
the actual local Weil group of the same field.
`FiniteEpsilon.LowerRankMaps` supplies a map from those Weil classes to the
supercuspidal classes at every allowed rank. `project` applies the map at
the stored rank and preserves that rank. Field universe `uF`, candidate
carrier universe `uC`, test carrier universe `uT`, and Weil carrier universe
`uW` remain independent. Only the map alias locally disables the universe
linter, because its two distinct carrier roles occur in a common maximum.
For the self-duality predicate, the local Hausdorff instance is the
published `TopologicalData.fieldT2`; the local nonarchimedean-ring instance
transports `ValuativeRel.nonarchimedeanRing` along
`Valuation.toTopologicalSpace_eq`. These are proved instance obligations,
not extra assumptions in the propositions.

Fix one `HarmonicAnalysis.UnitaryAdditiveCharacter` and one
`HarmonicAnalysis.AdditiveHaarMeasure` before candidates and tests are
quantified. The character type includes continuity and nontriviality.
Every component explicitly requires `HarmonicAnalysis.IsSelfDual ψ ν`.
This is the convention of Henniart 1993, pp.339–340, and the underlying
JPSS formulas. There is no conductor-zero requirement and no normalization
of the integer-ring volume to one. The module makes no assertion about
existence of factors for arbitrary non-self-dual measures.

`FiniteEpsilon.Agree F ψ ν π π' t` means that there exists a common
`e : ℂˣ × ℤ` satisfying both actual
`RankinSelberg.IsClassEpsilonFactor F ψ ν π t.2 e` and the relation for
`π'`. The witness describes the entire epsilon monomial, not its value at a
single spectral argument. Each test can have its own witness. The
candidate-first order is that of Henniart 1993; Henniart 2000 prints the
test-first order in its later formulas, whose use requires a separate
symmetry/comparison result.

The owner relation fixes the actual residue cardinality and normalized
absolute value, descends from actual JPSS equations via representation
equivalence, and includes existence of a compatible test-rank quotient
measure and nonzero Whittaker functionals. It requires the equation for
every such measure and pair of functionals; the additive block measures
are derived from the fixed `ν`. No missing measure or functional is treated
as an epsilon witness. The helper `Agree` asserts existence of a common
witness, rather than a vacuous implication between nonexistent witnesses.
The owner supplies intrinsic invariance and uniqueness; factor existence
and the local converse remain separate obligations.

## The three components

`FiniteSupercuspidalEpsilonSeparationStatement F` says that for every fixed
character and self-dual measure, every `k`, and every finite set `P` of
rank-`k+2` supercuspidal classes, there is a finite test family `D`.
`FiniteEpsilon.Separates` then requires that two members of `P` agreeing
at every member of `D` are equal. The order is
`∀ P, P.Finite → ∃ D, ∀ π ∈ P, ∀ π' ∈ P, ...`.
The family is independent of the compared pair. Empty and singleton sets
are allowed. No central-character condition is added to this component.

`SupercuspidalStratumEpsilonSeparationStatement F` takes the exact published
`SupercuspidalBoundedLevelFinitenessStatement` as a premise and asserts the
same finite separation for
`GeneralLinear.SupercuspidalClass.centralLevelStratum χ b`.
Here `χ` is a character of the actual center of `GL_(k+2)(F)` and `b` bounds
the first nonzero last-row fixed level. The stratum and finiteness
declarations are the existing owner interfaces. The first-level invariant
takes values in `WithTop ℕ`; it is not identified with an epsilon conductor.
This wrapper uses the published finiteness proposition as a hypothesis,
not as a proved result.

`FiniteSupercuspidalEpsilonLiftingStatement F` starts with `P`, a finite
separating family `D`, and supplied maps `lower`. It assumes surjectivity
at every `r : Fin (k+1)` and obtains a finite family `S` of actual Weil
classes. `FiniteEpsilon.ExactImage` says both that every selected lift
projects into `D` and that each member of `D` has a selected lift.
`FiniteEpsilon.LiftedSeparates` states separation by evaluating each lift
at its supplied supercuspidal image. Again `S` is chosen before the
compared candidate pair. This lifting component needs no additional
finiteness assumption on `P`, because `D` is already finite and separating.

## Scope

These are Prop-valued definitions, not proofs of existence of separating
families. The intended finite-separation argument uses the local converse
and finite selection; factor existence and uniqueness identify the common
witness relation with equality of epsilon factors. The stratum application
also uses its explicit bounded-level finiteness premise. The lifting argument
uses finite choice under the supplied surjections and needs no new analytic
input. The lifting statement does not construct the lower-rank maps, assert injectivity,
assume a rank-`k+2` correspondence, or compare with arithmetic tensor
epsilon factors. Its conclusion evaluates only at the supplied images.

Rank-one reciprocity, finite-order normalization by unramified twists,
conductor-to-first-level comparison, local finiteness proofs, arithmetic
factor comparison, common Galois enlargement, independence of global
choices, and numerical/rank induction remain outside this unit. In
particular, the unrestricted lower-rank surjections used here are those
of the 1993 formulation; the extra finite-order normalization in
Henniart 2000 Section 4.3 is not silently included.

