# Complex-place parameters of cyclic weak transfers

Worker 230 authored the proposition definitions
`Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceStatement`
and
`Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceTCStatement`.
They formulate B7 of the registered operator plan in the Library's actual
complex-place parameter vocabulary, together with the unitary-isobaric
base-change clause used along standard-B6 chains. The universe order of
both declarations is `uF uE uV uW`.

## Sources and scope

The registered source `operator-external-inputs-plan-2026-11-16`,
*Formalizing the large external inputs of the local Langlands correspondence
for GL_n* (16 November 2026), Section 2.2 B7 (TeX line 199), asks for
complex-place compatibility of weak base change and the Langlands sum for
the regular-orbit weak induction of B2. Section 4.6, “Interface,” identifies
these as consequences of Arthur–Clozel III.5.1 at a split archimedean place.
Section 4.8, “The infinity type” (lines 910–911), explains their use in
reading the infinity type of a descent.

Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989), registered as `arthur-clozel-1989-base-change`,
Chapter III, Theorem 5.1, printed p.212 / one-based PDF p.226, upgrades weak
lifting to strong lifting for representations induced from cuspidal ones,
under the assumptions of III.4.2. Definition III.4.1 and Theorem III.4.2(c),
printed p.202 / PDF p.216, describe induction from unitary cuspidal data and
the corresponding weak base change; these motivate the isobaric clause.
The parameter-list formulation of that clause is an internal extension of
the literal cuspidal B7 interface for the supplied standard-B6 chains.

These are sources for later compatibility proofs. This module defines two
propositions; it supplies no proof of either compatibility proposition.
The selected-coordinate and ordered-list conventions are internal, using
the existing actual completion-map comparisons. The elementary support
lemma in `ComplexPlaceParameterTransportInvolution` proves only that the
list transport is an involution.

## Common hypotheses and parameter meaning

Both targets quantify actual number fields `F : Type uF` and `E : Type uE`,
with `[Algebra F E]`, `[IsGalois F E]`, a cyclic automorphism group
`[IsCyclic (E ≃ₐ[F] E)]`, and prime degree
`(Module.finrank F E).Prime`. They retain
`[CompactSpace (AdeleQuotient F)]` and
`[CompactSpace (AdeleQuotient E)]`, as required by the cuspidal realization
and isobaric data interfaces. After the prime-degree hypothesis, the
conclusion is a conjunction of the three clauses below.

The TC target additionally assumes `[NumberField.IsTotallyComplex F]`.
Its three clauses are otherwise literally the same; it adds no separate
totally complex hypothesis on `E`.

All places are actual places:
`v : {v : NumberField.InfinitePlace F // v.IsComplex}` and
`w : InfinitePlacesAbove E v.1`. The operation `complexPlaceAbove v w`
packages the existing underlying place `w.1` as complex. In the selected
coordinates, `complexPlaceParameterTransport v w ds` returns `ds` if

```lean
w.1.embedding.comp (algebraMap F E) = v.1.embedding
```

and otherwise returns `ds.map ComplexCharacterData.conj`. The existing
conjugation precomposes the actual character with complex conjugation,
negates its integer weight and keeps its exponent. The completion-map
formulas
`Langlands.Global.HarrisDatum.extensionEmbedding_completionMap_of_eq` and
`Langlands.Global.HarrisDatum.extensionEmbedding_completionMap_of_ne`
justify exactly this identity/conjugation convention. Both operations
retain order and all occurrences of parameter blocks.

The cuspidal predicate `IsoClass.HasComplexPlaceParameter` is the existing
literal predicate. For a class of rank `n`, it requires a list of length
`n` and an injective complex-linear map from the `U(n)`-finite functions
of its complex standard module into the operator realization. That map
carries the standard compact action and the right derivatives in real
Lie algebra directions to the actual actions at the selected complex
place. It is a statement about these actual K-finite standard-module
embeddings. This module does not replace that predicate by its
permutation closure.

For isobaric data, `IsobaricData.HasComplexPlaceParameter` enumerates all
actual positive-rank cuspidal constituents with their multiset
multiplicities, attaches a literal parameter list to each constituent,
and takes the permutation closure of their flattened aggregate. Thus it
retains repeated constituents and repeated characters while allowing the
aggregate list in any order.

## The three clauses

1. **Cuspidal weak base change in both directions.** For
   `S : CuspidalOperatorRealization F r` and
   `T : CuspidalOperatorRealization E r`, assume
   `HasUnitaryCentralCharacter S` and
   `IsoClass.IsWeakBaseChangeOf.{uF,uE,uV,uW} T.isoClass S.isoClass`.
   For every `v`, every actual `w` above it and every supplied list `ds`,
   the clause asserts

   ```lean
   S.isoClass.HasComplexPlaceParameter v ds ↔
     T.isoClass.HasComplexPlaceParameter (complexPlaceAbove v w)
       (complexPlaceParameterTransport v w ds)
   ```

   Unitarity is imposed downstairs, on `S`. Both sides use the same
   supplied list, transported by the indicated coordinate operation.
   In particular, for a known upstairs list `us`, applying this equivalence
   to `complexPlaceParameterTransport v w us` and using the separate
   involution lemma recovers the downstairs parameter list.

2. **B2 regular-orbit weak induction.** For
   `S : CuspidalOperatorRealization F r` and
   `T : CuspidalOperatorRealization E m`, assume
   `HasUnitaryCentralCharacter T`,
   `∀ σ : E ≃ₐ[F] E, σ ≠ 1 → ¬ T.isoClass.IsGaloisStable σ`, and
   `IsoClass.IsWeakInductionOf.{uF,uE,uV,uW} S.isoClass T.isoClass`.
   Thus the unitary input is upstairs and every nonidentity Galois
   automorphism gives a distinct conjugate. This is the generator-free
   regular-orbit condition for B2; conversion from its powers-of-a-generator
   formulation in the prime cyclic group is a downstream branch-proof
   obligation.

   Given `v`, `d : ℕ`, a genuine enumeration
   `e : Fin d ≃ InfinitePlacesAbove E v.1`, and a family of supplied lists
   `ds : InfinitePlacesAbove E v.1 → List ComplexCharacterData`, parameters
   for `T` at every `complexPlaceAbove v w` imply a parameter for `S` at
   `v`, with list `complexPlaceLanglandsSum v e ds`. This is precisely

   ```lean
   (List.ofFn (fun i : Fin d =>
     complexPlaceParameterTransport v (e i) (ds (e i)))).flatten
   ```

   Each actual place appears exactly once because `e` is an equivalence.
   Every block occurrence is retained. The displayed literal list follows
   the order selected by `e`; the clause quantifies every such enumeration.
   No arbitrary list of places or separate equality `d = Module.finrank F E`
   replaces the equivalence.

   The cuspidal ranks are `r+1` and `m+1`. The existing weak-induction
   relation already carries their comparison
   `r+1 = (m+1) * Module.finrank F E`; the statement adds no independent
   rank convention.

3. **Unitary-isobaric weak base change in both directions.** For arbitrary
   `DF : IsobaricData F` and `DE : IsobaricData E`, assume `DF.IsUnitary`,
   `DE.IsUnitary`, and
   `IsobaricData.IsWeakBaseChangeOf.{uF,uE,uV,uW} DE DF`.
   For every `v`, every actual `w` above it and every supplied aggregate
   list `ds`, the clause asserts

   ```lean
   DF.HasComplexPlaceParameter v ds ↔
     DE.HasComplexPlaceParameter (complexPlaceAbove v w)
       (complexPlaceParameterTransport v w ds)
   ```

   Both unitary hypotheses are explicit. This covers the general unitary
   isobaric entries of standard-B6 chains, including their multiplicities;
   it is not restricted to a single cuspidal constituent. The published
   singleton lemma for the aggregate predicate connects the cuspidal
   start to this clause. Comparing the terminal datum with actual Hecke
   parameters is a separate endpoint statement.

All three clauses retain the Library's existing weak finite-place transfer
relations, defined through attached spectral systems and almost-everywhere
unramified data. Neither target has an E2-map parameter. The compatibility
conclusion is additional information at complex places, not something
proved here from the definition of a weak transfer.

## Separate archimedean and structural obligations

B7 compares supplied actual parameters. It does not assert that every
cuspidal class has parameters, that they determine an infinitesimal
character, or that a numerical integral/regular condition is equivalent
to the Library's regular-algebraicity predicate. Universal parameter
existence, infinitesimal-character determination and the Clozel
integral/regular criterion belong to the separate authorized archimedean
bridge, normalized against `ArchimedeanGL.IsRegularAlgebraicCharacter`.
Downstream statements must retain that bridge as separately named
premises when deriving regular-algebraicity conclusions.

The involution helper suffices for reversing transport across one step.
Composition of transport along towers and arithmetic transport through
endpoint field equivalences remain structural obligations of the later
branch proofs. Any conditional assembly from a general III.5.1 premise
also remains separate from a proof of that premise.
