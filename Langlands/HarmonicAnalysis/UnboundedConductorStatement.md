# Unbounded conductors of actual p-adic quasicharacters

The module `Langlands.HarmonicAnalysis.UnboundedConductorStatement` defines
`Langlands.HarmonicAnalysis.PadicQuasicharacterUnboundedConductorStatement.{uF}`.
It is a closed proposition definition, with an arbitrary independent field
universe `uF`. It asserts that for every prime `p`, every finite extension
`F : PadicField.{uF} p`, and every natural number `A`, there is a continuous
complex quasicharacter of the actual field-unit group whose multiplicative
conductor is at least `A`.

Its complete formula is:

```lean
∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (A : ℕ),
  ∃ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
    A ≤ F.canonicalTopologicalData.multiplicativeConductor χ
```

The quantifier over `F` includes every field carrier in universe `uF` and
all finite extension degrees. `PadicField` supplies its field, specified
`Padic p` algebra, and finite-dimensional structure. The local `letI` fixes
the domain topology to `F.canonicalTopologicalData.topology`; no topological
realization is an additional argument. The conductor uses that same canonical
topological data, including its actual valuation. The target complex units
carry their existing topology.

`Quasicharacter F.Carrier` is the published abbreviation for
`ContinuousMonoidHom F.Carrierˣ ℂˣ`, so the existential conclusion supplies
a genuine continuous homomorphism. Its existence is part of the conclusion.
The statement does not restrict the witness to finite order, unitarity or
nontriviality. In particular `A = 0` is included. Applying the proposition at
`A + 1` supplies conductor strictly greater than `A`; the weak inequality
in the definition directly matches the high-ramification consumer threshold.

## Conductor convention and dependencies

The direct project imports are `Langlands.HarmonicAnalysis.Conductor` and
`Langlands.LocalField.Canonical`. The first imports
`Langlands.HarmonicAnalysis.Basic`, which supplies the character type. The
second supplies `PadicField.canonicalTopologicalData`. No imported definition
or consumer statement is changed.

For `T = F.canonicalTopologicalData`, the subgroup `T.principalUnits n` is
defined on the actual field units by

```text
T.discreteValuation u = 1
and T.discreteValuation (u - 1) ≤ WithZero.exp (-(n : ℤ)).
```

At `n = 0` this is the full integral-unit group `O_Fˣ`; for positive `n`
it is `1 + π^n O_F`. Thus the filtration is an actual valuation-defined
subgroup, rather than arbitrary supplied filtration data.
`T.MultiplicativeTrivialAt χ n` means that `χ` is one on this subgroup.
`T.multiplicativeConductor χ` is `Nat.find` of the already proved
`T.exists_multiplicativeTrivialAt χ`. It is the least natural level of
triviality, including zero. The published law
`T.multiplicativeTrivialAt_iff_conductor_le χ n` states exactly that
triviality at `n` is equivalent to conductor at most `n`.
`T.multiplicativeConductor_eq_zero_iff χ` identifies zero conductor with
being unramified, meaning triviality on all integral units.

These results establish the conductor for each fixed character. They do
not establish its unboundedness as the character varies. The new module
contains only the proposition definition and supplies no proof or chosen
character.

## Internal provenance and original sources

This is an internal elementary local-field prerequisite, formulated for
selecting sufficiently ramified rank-one characters in the JPSS
Rankin-Selberg arguments. It is not claimed to be a verbatim or exact
transcription of a named result in JPSS.

The motivating original is H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg convolutions*, American Journal of Mathematics
105 (1983), 367–464, registered source `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained file is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
Proposition 2.13, printed page 404 (retained PDF page 39), gives the
sufficient-conductor threshold for twisted pair L-factor vanishing and
says it is used in section 7. Section 9.3, printed page 457 (retained PDF
page 92), selects highly ramified quasicharacters to remove the extra
rank-one L-factors in a divisibility argument. Both original pages were
read visually. They motivate the need to supply actual characters beyond
a threshold; they are not used as a proof of this existence proposition.

The conductor convention is John Tate, *Number theoretic background*, in
*Automorphic Forms, Representations and L-Functions*, Proceedings of Symposia
in Pure Mathematics 33, Part II (1979), 3–26, section 3.2.6, printed page 13
(retained PDF page 22), registered source
`tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The retained file is
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
The original page was read visually: Tate sets `a(χ) = 0` in the unramified
case and otherwise takes the smallest unit-congruence level of triviality.
This is the convention implemented by the imported Library conductor.
No source-specific errata note for either registered source was found in
the current public Library notes or shared public-note locations at authoring.

## Remaining proof obligation and scope

A later proof must construct actual continuous characters and establish
these conductor lower bounds. Finite unit quotients, character separation,
and extension to the full field-unit group are possible proof ingredients,
not hypotheses of this proposition. The proposition has no reciprocity
family, additive character, Haar measure, representation classification,
local Langlands correspondence, finite extension tower, character-extension
or separation theorem, filtration-strictness certificate, or existing
high-conductor existence assertion as an input.

Rank-one Whittaker-type certificates, high-ramification L-vanishing, and
factor multiplicativity are separate results. In particular the existing
`Langlands.RankinSelberg.WhittakerTypeHighlyRamifiedLVanishingStatement`
supplies a threshold for all characters beyond it and does not itself
supply a character meeting it. The present statement supplies precisely
that existence conclusion when later proved, independently of L-factors.

Worker 455 authored the Lean and Markdown pair. Worker 53 supplied the
concrete statement specification and consumer scope in the task contract.
Compilation and inspection are development checks; mathematical statement
acceptance requires independent semantic review and Library publication.
