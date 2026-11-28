# B7 and its totally complex form from strong cyclic base change

Module `Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceReductionProof`. It
proves two implications of the module
`Langlands.Automorphic.Unramified.StrongBaseChangeSupportReductionStatement`, each with its
universe parameters `uF uE uV uW` left free:

- `cyclicWeakBaseChangeComplexPlaceReduction : CyclicWeakBaseChangeComplexPlaceReductionStatement`,
  that is,
  `CyclicStrongBaseChangeSupportStatement.{uF, max uF uE, uF, uE, uV, uW} →
  CyclicWeakBaseChangeComplexPlaceStatement.{uF, uE, uV, uW}` (B7);
- `cyclicWeakBaseChangeComplexPlaceReductionTC :
  CyclicWeakBaseChangeComplexPlaceReductionTCStatement`, the same implication with the totally
  complex form `CyclicWeakBaseChangeComplexPlaceTCStatement` as conclusion.

Each implication assumes the named external premise `CyclicStrongBaseChangeSupportStatement`,
the Library formulation of the support and parameter consequences of Arthur–Clozel, Theorem
III.5.1; this module does not prove the premise. The premise is a conjunction of four clauses
(N′, S, C and R), and the proof projects the complex-place clause C from it (`hBC.2.2.1`): for a cyclic extension
`E/F` of prime degree, unitary isobaric data `DF`, `DE` with
`IsobaricData.IsWeakBaseChangeOf DE DF`, a complex place `v` of `F` and a place `w` of `E` above
`v`, `DF` has the aggregate parameter `ds` at `v` if and only if `DE` has
`complexPlaceParameterTransport v w ds` at `w`. The clauses N′, S and R, the local base-change
maps at finite places, the canonical or restricted B7 and any trace formula are not used. All
other inputs are proved Library theorems; those not in earlier modules are in
`Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceComparisons` (see its
Markdown).

## The proof

Fix `F`, `E`, the instances of the statement and the primality of `[E : F]`, and let `C` be
clause C of the premise at these fields (its universe levels for presentations are `uV` over `F`
and `uW` over `E`, those of the conclusion).

**Clause (1).** Let `S` over `F` and `T` over `E` be cuspidal realizations of the same rank, `S`
with unitary central character and the class of `T` a weak base change of the class of `S`.

- `T` has unitary central character by `hasUnitaryCentralCharacter_of_isWeakBaseChangeOf`
  (clause (1) assumes nothing on `T`).
- Both realizations are then unitarizable
  (`CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter`), so their
  singleton data are unitary (`IsobaricData.isUnitary_ofCuspidal`).
- The singleton of `T` is a weak base change of the singleton of `S`
  (`IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff`).
- `C` applied to the two singletons compares their aggregate parameters at `v` and at `w`.
  `IsobaricData.hasComplexPlaceParameter_ofCuspidal_iff`, on both sides, replaces the aggregate
  parameters of the singletons by the literal parameters of `S` and `T`. That theorem combines
  `IsobaricData.hasComplexPlaceParameter_ofCuspidal` with the reordering of literal parameters
  `PositiveRankCuspidalClass.hasComplexPlaceParameter_of_perm`.

**Clause (2).** Let `T` over `E` have unitary central character and let the class of `S` over
`F` be weakly induced from the class of `T`. Let `v` be a complex place of `F`, `e` an
enumeration of the places of `E` above `v`, and `ds w'` a literal parameter of `T` at each place
`w'` above `v`. The hypothesis that `T` is not Galois-stable is not needed.

- `S` has unitary central character by the Library theorem `weakInductionUnitaryCentralCharacter`
  (module `WeakInductionUnitaryCentralCharacter`), so its singleton datum is unitary.
- The Galois orbit datum `IsobaricData.galoisOrbit F` of the class of `T` is unitary
  (`isUnitary_galoisOrbit_of_hasUnitaryCentralCharacter`).
- The orbit datum is a weak base change of the singleton of `S`: this is the Library theorem
  `weakInductionOrbitBaseChange`, which proves `WeakInductionOrbitBaseChangeStatement` (statement
  in `CyclicOrbitInductionComparisonStatement`, proof in `WeakInductionOrbitRestriction`).
- Choose a place `w` above `v` (`nonempty_infinitePlacesAbove`). By the orbit parameter
  `galoisOrbit_hasComplexPlaceParameter`, the orbit datum has at `w` the aggregate parameter
  `complexPlaceParameterTransport v w (complexPlaceLanglandsSum v e ds)`.
- The reverse direction of `C` gives the aggregate parameter
  `complexPlaceLanglandsSum v e ds` of the singleton of `S` at `v`, and
  `IsobaricData.hasComplexPlaceParameter_ofCuspidal_iff` turns it into the literal parameter of
  `S`.

**Clause (3)** is `C` itself.

**Totally complex form.** `cyclicWeakBaseChangeComplexPlaceReductionTC` forgets the instance
`NumberField.IsTotallyComplex F` and applies `cyclicWeakBaseChangeComplexPlaceReduction` with
the same premise.

## Sources

- J. Arthur and L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Ann. of Math. Studies 120 (1989), source ID `arthur-clozel-1989-base-change` (PDF
  page = printed page + 14): Chapter III, Definitions 1.1–1.2 (weak and strong lifting),
  printed p. 199; Definition 4.1 and Theorem 4.2, printed p. 202; Theorem 5.1 (a weak lifting
  between representations induced from cuspidal is a strong lifting), printed pp. 212–213.
  Strong lifting (Definition 1.2) is a condition at every place, finite or infinite, and
  Theorem 5.1 has the prime cyclic, induced-from-unitary-cuspidal scope of Definition 4.1 and
  Theorem 4.2. Clause C of the premise expresses the complex-place parameter compatibility
  associated with Theorem 5.1; the proof applies it to cuspidal singletons and to a Galois
  orbit.
- Operator note `operator-external-inputs-plan-2026-11-16` (*Formalizing the large external
  inputs of the local Langlands correspondence for GL_n*, 16 November 2026, file
  `external-inputs-plan.tex`): Section 2.2, item B7 (TeX line 199); Section 4.6, the interface
  paragraph (TeX line 737: B7 is a consequence of III.5.1 at a place that splits); Section 4.8,
  the paragraph on the infinity type (TeX line 910).
