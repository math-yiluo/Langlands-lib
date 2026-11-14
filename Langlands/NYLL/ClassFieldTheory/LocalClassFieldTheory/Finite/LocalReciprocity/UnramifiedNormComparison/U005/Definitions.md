# The unramified Galois group and its abelianization

This module adapts NYLL source unit M267.005 as the data definition
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupEquivAbelianizationOfUnramifiedValuation`.
For a finite Galois unramified extension of nonarchimedean local fields, it
constructs the multiplicative equivalence
`Gal(L / K) ≃* Abelianization (Gal(L / K))`. Its forward map is Mathlib's
canonical projection `Abelianization.of`. The computation theorem M267.006
is a separate unit.

## Parameters

The source telescope is retained in full and in order. Both `K` and `L`
have type `Type` (universe zero), with `Field`, `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField` instances. The remaining
parameters are:

```lean
[Algebra K L] [FiniteDimensional K L] [IsGalois K L]
[Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]
[IsIntegralClosure 𝒪[L] 𝒪[K] L]
[Module.Finite 𝒪[K] 𝒪[L]]
[IsUnramifiedValuedExtension K L]
```

Here the unramified class is the published
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`
(M161.001). It asserts that the ramification index of the maximal ideal
of `𝒪[L]` over `𝒪[K]` is one. The valuation-extension instance provides the
integer-ring and residue-field algebras. The integral-closure and finite-module
hypotheses retain their source meaning; no new hypothesis supplies cyclicity,
commutativity or the desired equivalence.

## Construction and imports

The source first installs cyclicity by M264.016, then the local commutative
group structure `IsCyclic.commGroup`, then returns
`Abelianization.equivOfComm`. This adaptation keeps the last two steps.
It supplies the first step directly using:

1. The published M161.036
   `Langlands.NYLL.LocalFieldTheory.galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure`,
   in module
   `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueEquivDefinitions`.
   This is the actual residue-action equivalence
   `Gal(L / K) ≃* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])`.
2. Mathlib's `MulEquiv.isCyclic`: cyclicity transports across a group
   equivalence. The residue-field automorphism group is cyclic by the instance
   at lines 408–413 of `Mathlib/FieldTheory/Finite/Basic.lean`, since the
   residue field of a nonarchimedean local field is finite.
3. Mathlib's `IsCyclic.commGroup` supplies a local `CommGroup` with the
   existing group operations.
4. `Abelianization.equivOfComm`, imported explicitly from
   `Mathlib.GroupTheory.Abelianization.Defs`, constructs the equivalence
   with forward map `Abelianization.of`.

The two `letI` instances exist only inside this definition. No cyclicity
theorem or global instance is exported. The only imports are the published
M161.036 module and Mathlib's abelianization definitions. This construction
does not require the rest of M264, M266, the finite reciprocity interface
M254, or the norm-valuation module M162.

Worker 3's shared M264.016 `CyclicProof` draft supplied the residue-equivalence
cyclicity argument. Worker 205 applied it internally to this definition;
the draft theorem itself is neither imported nor duplicated.

## Source correspondence and modifications

The pinned original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean#L94-L101)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file SHA-256
`a955313b05e5cdeb8bd4e9c6c76e466c956fe7231bb6fd90f4945a57e564ad26`.
The declaration is at lines 95–101, with its doc comment at line 94; the
shared section parameters are at lines 35–47. Its original name is
`LocalClassFieldTheory.galoisGroupEquivAbelianizationOfUnramifiedValuation`.

Worker 205 made these changes on 14 November 2026: extract only this
definition, prefix the namespace with `Langlands.NYLL`, replace broad source
imports by the two focused imports above, and replace the proof of the local
cyclicity instance as described above. The source Type-0 parameter telescope,
result type, local commutative-group construction and final equivalence are
unchanged. The source copyright and author header and the source doc comment
are retained.

## Checks

The focused `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled this module with no
errors or warnings. Exact inspection of the definition reported no universe
parameters and only `propext`, `Classical.choice` and `Quot.sound`. This
successful focused check establishes that the two imports above suffice
without M264.016 or the source module's other dependencies. Development
compilation does not constitute independent acceptance.

## Provenance and license

The original belongs to registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Apache-2.0 license and notices are retained as
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` in the Library.
