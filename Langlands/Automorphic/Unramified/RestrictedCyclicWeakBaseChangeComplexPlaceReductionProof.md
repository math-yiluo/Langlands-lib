# Restricted B7 from the restricted complex-place compatibility

Module `Langlands.Automorphic.Unramified.RestrictedCyclicWeakBaseChangeComplexPlaceReductionProof`.
The theorem `restrictedCyclicWeakBaseChangeComplexPlaceReduction` proves
`RestrictedCyclicWeakBaseChangeComplexPlaceReductionStatement` (module of the same name) with its
universe parameters `uF uE uV uW` left free:

```lean
RestrictedCyclicBaseChangeComplexPlaceCompatibilityStatement.{uF, uE, uV, uW} →
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{uF, uE, uV, uW}
```

The implication assumes the named premise
`RestrictedCyclicBaseChangeComplexPlaceCompatibilityStatement`, the restricted complex-place
compatibility; this module does not prove the premise. For a CM field `F`, a cyclic extension `E/F` of
prime degree, an auxiliary finite place `v₀ ≠ v̄₀` with single places `w₀`, `wc` of `E` above
`v₀` and `v̄₀`, a cuspidal realization `S` over `F` with unitary central character that is
supercuspidal at `v₀` and `v̄₀`, and unitary isobaric data `D` over `E` that is a weak base change
of the singleton of the class of `S`, it says: at every complex place `v` of `F` and place `w`
of `E` above `v`, the singleton has the aggregate parameter `ds` at `v` if and only if `D` has
`complexPlaceParameterTransport v w ds` at `w`. No other premise is used, nor canonical or
restricted B7, nor any local base-change map or trace formula. The remaining inputs are proved
Library theorems; those not in earlier modules are in
`Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceComparisons` (see its
Markdown).

## The proof

Fix the fields, the instances, the primality of `[E : F]` and the auxiliary data `v₀`, `w₀`,
`wc` with their hypotheses; they are passed unchanged to the premise.

**Clause (1)r.** Let `S` over `F` and `T` over `E` be cuspidal realizations of the same rank,
both with unitary central character, `S` supercuspidal at `v₀` and `v̄₀`, and the class of `T` a
weak base change of the class of `S`. Take `D` to be the singleton of the class of `T`.

- `D` is unitary (`CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter`
  and `IsobaricData.isUnitary_ofCuspidal`).
- `D` is a weak base change of the singleton of `S`
  (`IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff`).
- The premise compares the aggregate parameters of the two singletons, and
  `IsobaricData.hasComplexPlaceParameter_ofCuspidal_iff` replaces them on both sides by the
  literal parameters of `S` and `T`. That theorem combines
  `IsobaricData.hasComplexPlaceParameter_ofCuspidal` with the reordering of literal parameters
  `PositiveRankCuspidalClass.hasComplexPlaceParameter_of_perm`.

The supercuspidality of `T` at `w₀` and `wc` is not used.

**Clause (2)r.** Let `S` and `T` be as in (2)r: both with unitary central character, `S`
supercuspidal at `v₀` and `v̄₀`, and the class of `S` weakly induced from the class of `T`. Let
`v` be a complex place of `F`, `e` an enumeration of the places of `E` above `v`, and `ds w'` a
literal parameter of `T` at each place `w'` above `v`. Take `D` to be the Galois orbit datum
`IsobaricData.galoisOrbit F` of the class of `T`.

- `D` is unitary (`isUnitary_galoisOrbit_of_hasUnitaryCentralCharacter`).
- `D` is a weak base change of the singleton of `S`: this is the Library theorem
  `weakInductionOrbitBaseChange`, which proves `WeakInductionOrbitBaseChangeStatement`
  (statement in `CyclicOrbitInductionComparisonStatement`, proof in
  `WeakInductionOrbitRestriction`).
- Choose a place `w` above `v` (`nonempty_infinitePlacesAbove`). By the orbit parameter
  `galoisOrbit_hasComplexPlaceParameter`, `D` has at `w` the aggregate parameter
  `complexPlaceParameterTransport v w (complexPlaceLanglandsSum v e ds)`.
- The reverse direction of the premise gives the aggregate parameter
  `complexPlaceLanglandsSum v e ds` of the singleton of `S` at `v`, which is the literal
  parameter of `S` by `IsobaricData.hasComplexPlaceParameter_ofCuspidal_iff`.

The supercuspidality of `T` and the hypothesis that `T` is not Galois-stable are not used.

## Sources

- J. Arthur and L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Ann. of Math. Studies 120 (1989), source ID `arthur-clozel-1989-base-change` (PDF
  page = printed page + 14): Chapter III, Definition 1.2 (strong lifting), printed p. 199;
  Definition 4.1 and Theorem 4.2, printed p. 202; Theorem 5.1, printed pp. 212–213. Strong
  lifting (Definition 1.2) is a condition at every place, and Theorem 5.1 has the prime cyclic,
  induced-from-unitary-cuspidal scope of Definition 4.1 and Theorem 4.2. The premise expresses
  the complex-place parameter compatibility associated with Theorem 5.1, for a cuspidal source
  in the restricted setting above; the proof applies it to a cuspidal singleton and to a Galois
  orbit.
- Operator note `operator-external-inputs-plan-2026-11-16` (*Formalizing the large external
  inputs of the local Langlands correspondence for GL_n*, 16 November 2026, file
  `external-inputs-plan.tex`): Section 2.2, item B7 (TeX line 199); Section 4.6, the interface
  paragraph (TeX line 737: B7 is a consequence of III.5.1 at a place that splits); Section 4.8,
  the paragraph on the infinity type (TeX line 910).
