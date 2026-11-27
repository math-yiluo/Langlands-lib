# Restricted B7 from the restricted complex-place compatibility

Module `Langlands.Automorphic.Unramified.RestrictedCyclicWeakBaseChangeComplexPlaceReductionStatement`,
namespace `Langlands.Automorphic.Unramified`. The module contains one proposition definition,
`RestrictedCyclicWeakBaseChangeComplexPlaceReductionStatement`, with universe parameters
`uF uE uV uW` in this order. It states an implication and proves neither the implication, nor
its premise, nor its conclusion.

## The statement

`RestrictedCyclicWeakBaseChangeComplexPlaceReductionStatement.{uF, uE, uV, uW}` is

```lean
RestrictedCyclicBaseChangeComplexPlaceCompatibilityStatement.{uF, uE, uV, uW} →
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{uF, uE, uV, uW}
```

Both propositions are published in their own modules and are not restated here.

- The premise, `RestrictedCyclicBaseChangeComplexPlaceCompatibilityStatement`, is the named
  premise of the restricted route to B7. For a CM field `F`, a cyclic extension `E/F` of prime
  degree, a finite place `v₀ ≠ v̄₀` (`Harris.conjPlace F v₀`) of `F` with single places `w₀`,
  `wc` of `E` above `v₀` and `v̄₀`, a cuspidal realization `S` over `F` with unitary central
  character that is supercuspidal at `v₀` and `v̄₀`, and unitary isobaric data `D` over `E`
  that is a weak base
  change of the singleton of `S.isoClass`, it says: at every complex place `v` of `F` and every
  place `w` of `E` above `v`, the singleton of `S.isoClass` has the aggregate parameter `ds`
  at `v` if and only if `D` has `complexPlaceParameterTransport v w ds` at `w`. It is the
  complex-place consequence of strong lifting (Arthur–Clozel, Theorem III.5.1) in this
  restricted setting. This module does not prove it.
- The conclusion, `RestrictedCyclicWeakBaseChangeComplexPlaceStatement` (restricted B7), has
  the same field and auxiliary-place data and two clauses on cuspidal classes `S` over `F` and
  `T` over `E`, both with unitary central character and supercuspidal at the auxiliary pair:
  (1)r, for `T.isoClass` a weak base change of `S.isoClass`, `S.isoClass` has the literal
  complex-place parameter `ds` at `v` if and only if `T.isoClass` has
  `complexPlaceParameterTransport v w ds` at `w`; (2)r, for `S.isoClass` weakly induced from
  a `T.isoClass` that is not Galois-stable under any `σ ≠ 1`, literal parameters `ds w` of
  `T.isoClass` at all places `w` above `v` give the literal parameter
  `complexPlaceLanglandsSum v e ds` of `S.isoClass` at `v`.

## Universe instantiation

Both propositions have the universe parameters `uF uE uV uW`: the fields `F` and `E`, and the
spectral presentations over `F` and over `E`. The premise is used at the levels of the
conclusion. In restricted B7 the supercuspidality of `S` is
`HasSupercuspidalComponent.{uF, uV}` and the weak base change and weak induction relations are
at `.{uF, uE, uV, uW}`. In the premise the supercuspidality of `S` is at `.{uF, uV}` and the
weak base change of isobaric data at `.{uF, uE, uV, uW}`. The upstairs data `D` used below are
built from `T.isoClass`, whose presentations are at `uW`.

## Intended derivation

This is a plan, not a proof. It follows the section "Relation to the restricted complex-place
premise" of the Markdown of `RestrictedCyclicWeakBaseChangeComplexPlaceStatement` and the
section "Conditional derivation of restricted B7" of the Markdown of the premise.

1. *Clause (1)r.* Take `D` to be the singleton of `T.isoClass`. It is unitary by
   `CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter` and
   `IsobaricData.isUnitary_ofCuspidal`. The weak relation passes by
   `IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff`. The hypotheses of the premise on `S`
   (unitary central character, supercuspidality at `v₀` and `v̄₀`) are hypotheses of (1)r; the
   supercuspidality of `T` is not used.
2. *Clause (2)r.* Take `D` to be the orbit datum `IsobaricData.galoisOrbit F` of the class of
   `T`, with one constituent for each Galois automorphism. It is unitary because every Galois
   conjugate of `T` is. It must be shown to be a weak base change of the singleton of
   `S.isoClass`, given the weak induction.
3. *Parameters.* The premise compares aggregate parameters, and restricted B7 literal ones.
   `IsobaricData.hasComplexPlaceParameter_ofCuspidal` identifies the aggregate parameter of a
   singleton with the literal parameter of a permutation of the list. For (2)r, transporting
   `complexPlaceLanglandsSum v e ds` from `v` to a place `w` above `v` must give the aggregate
   list of the orbit datum up to `List.Perm`; the reverse direction of the premise then gives
   the aggregate parameter of the singleton of `S.isoClass` at `v`.

The four comparisons this needs, none of them proved in this module, are those listed in the
Markdown of restricted B7:

- *singleton comparison*: the aggregate predicate of a singleton is the permutation closure of
  the literal predicate;
- *parameter-order comparison*: from a literal parameter for a permutation of a list to a
  literal parameter for the list itself;
- *weak-transfer comparison*: the cuspidal and isobaric weak base change relations on
  singletons, and unitary central character against isobaric unitarity;
- *orbit-induction comparison*: the orbit datum of `T` is a weak base change of a class weakly
  induced from `T`, including at inert unramified places, and the transported Langlands sum
  matches its aggregate parameter.

The derivation uses the premise only at complex places, where every place of `E` above `v`
is split; it needs no local base-change map at finite places.

## Sources

- J. Arthur and L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Ann. of Math. Studies 120 (1989), source ID `arthur-clozel-1989-base-change` (PDF
  page = printed page + 14): Chapter III, Definition 1.2 (strong lifting), printed p. 199;
  Definition 4.1 and Theorem 4.2, printed p. 202; Theorem 5.1, printed pp. 212–213.
- Operator note `operator-external-inputs-plan-2026-11-16` (*Formalizing the large external
  inputs of the local Langlands correspondence for GL_n*, 16 November 2026, file
  `external-inputs-plan.tex`): Section 2.2, item B7 (TeX line 199); Section 4.6, the interface
  paragraph (TeX line 737: B7 is a consequence of III.5.1 at a place that splits); Section 4.8,
  the paragraph on the infinity type (TeX line 910).
