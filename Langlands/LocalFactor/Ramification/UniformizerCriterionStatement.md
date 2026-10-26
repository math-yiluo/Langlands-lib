# The uniformizer test for actual lower ramification groups

Authors: Worker 507, with Worker 32's formulation and derivation.

`Langlands.Ramification.Padic.UniformizerCriterion.{u,v}` is a proposition
target. This pair states the criterion; it does not prove it.

For each prime `p`, the fields `F : PadicField.{u} p` and
`E : PadicField.{v} p` have independent carrier universes. The given
`Algebra F.Carrier E.Carrier` is compatible with their p-adic base
structures through `IsScalarTower (Padic p) F.Carrier E.Carrier`.
The data `T : F.TopologicalData` and `S : E.TopologicalData` are arbitrary
supplied realizations. Assume that the actual map
`PadicField.TopologicalData.relativeResidueMap T S` is surjective.
For every `π : E.Carrier` with `S.ord π = 1`, every base-field
automorphism `σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier`, and every natural
number `i`, the target says

```text
σ ∈ lowerRamificationGroup S F.Carrier i
  ↔ σ π - π = 0 ∨ (i + 1 : ℤ) ≤ S.ord (σ π - π).
```

Here `lowerRamificationGroup` is the existing construction in
`Langlands.LocalFactor.Ramification.Galois`. It restricts the actual field
automorphisms to `S.Integers`, and tests
`integerAutomorphism S F.Carrier σ x - x` for membership in
`IsLocalRing.maximalIdeal S.Integers ^ (i + 1)` for every integer `x`.
The relative residue map is the existing induced map on the residue fields
of the supplied integer rings in `Langlands.LocalField.RelativeIntegers`.
The order is the existing normalized additive integer-valued `S.ord`.
There is no replacement action, integer ring, residue field, or order.

The residue-map surjectivity is the total-ramification input. It is an
explicit hypothesis, with no assertion that arbitrary extensions satisfy
it. The proposition assumes no Galoisness, generation theorem, lower-group
comparison, or extra supplied action. The index includes `i = 0`;
the uniformizer is arbitrary, rather than restricted to `S.uniformizer`.
The statement concerns one lower-ramification test, and does not assert an
unramified base-change comparison.

The zero disjunct is necessary. The published convention is `S.ord 0 = 0`,
whereas the usual extended valuation assigns infinite order to zero.
Consequently an order inequality alone would fail even for the identity
automorphism. For a nonzero displacement, the bound is exactly `i + 1`;
for a zero displacement, the disjunct records congruence modulo every
maximal-ideal power.

The provenance is a derived form of Jean-Pierre Serre, *Local Fields*,
English translation by Marvin Jay Greenberg, GTM 67, Springer (1979),
Chapter IV, section 1, Lemma 1 and Proposition 1, printed pages 61–62
(PDF pages 68–69), and section 2, Proposition 5, printed page 66
(PDF page 73). The preceding notation on printed page 65 (PDF page 72)
chooses an arbitrary uniformizer. Worker 507 read these original pages
and rendered PDF page 73 to check the ideal-power exponent.
Registered original: `serre-1979-local-fields`, at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Serre works with a finite Galois extension and formulates Proposition 5
for an element of inertia, using `σ(π)/π ≡ 1` modulo the `i`th
maximal-ideal power. In the totally ramified case inertia is the whole
Galois group. Multiplying the displacement by `π`, whose order is one,
gives the additive bound `v(σ(π) - π) ≥ i + 1`. His section 1
identifies this with acting trivially on the integer ring modulo the
`(i + 1)`st maximal-ideal power.

The present formulation is stronger in that it does not assume Galoisness.
This generality is derived from the same congruence mechanism, rather than
claimed as Serre's literal wording. Surjectivity of the actual relative
residue map lets one lift the residue of each extension integer to a base
integer, which every base-field automorphism fixes. Subtracting this lift
leaves a multiple of any chosen uniformizer. Induction on the ideal-power
exponent then propagates the uniformizer congruence to all integers;
the reverse direction evaluates the all-integer congruence at that
uniformizer. This argument motivates the target without adding a
generation or Galois hypothesis. Its formal implementation remains the
proof successor's obligation.

Worker 507 also read the *Local Fields* entries on PDF pages 2–3 of
Serre's *Corrections to J-P. Serre's books* (2019), registered as
`serre-book-corrections-2019`, SHA-256
`b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`.
Those entries make no correction to the cited statements on printed
pages 61–62 and 66. The retained errata file is
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`.

The imported constructions retain their original authorship. In
particular, the relative integer and residue maps are Worker 90's work;
this statement pair contains no adaptation of their proofs. The pinned
environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
