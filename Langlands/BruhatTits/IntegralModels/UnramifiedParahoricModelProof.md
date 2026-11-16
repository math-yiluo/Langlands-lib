# Proof of the unramified parahoric model statement

`Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel` proves exactly
`Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement.{u}`
at arbitrary universe `u`, by composing published Library proofs and
assemblies.

For a nonarchimedean local field `F`, write `K = inertiaFixedField F` and
`O = fixedFieldIntegers F`. Given the affine group `G` over `F`, the
supplied building datum `C` and original zero datum `E` for `G_K`, a
rational point `g` and a nonempty bounded apartment subset `Ωa`, the
conclusion supplies actual `RelativeComponentModelData O K G_K`. This
contains a smooth affine full model, its smooth affine relative identity
component with connected fibres, and their inclusion. For
`Ω = (fun x => g • C.apartmentMap x) '' Ωa`, their integral-point images
are exactly

```text
D.full.integralPoints =
  characterValuationKernel (MaximalUnramified.valuation F) G_K ⊓ C.pointwiseFixer Ω
D.neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer Ω.
```

Boundedness has the target's meaning: every real affine function is bounded
above on `Ωa`. The proof preserves every quantifier of the published
statement, including every supplied `C`, `E` and translated apartment.

The source comparison for KP Theorems 8.3.2 and 8.3.13, including the
registered corrections to Section 8.3 and the precise scope of the
statement, is in
[the unchanged target Markdown](UnramifiedParahoricModelStatement.md).
The present proof is a derived composition of the following Library
results.

The local proof `hLift` applies
`unramifiedTorusNeutralSurjectivityAssembly` to four unconditional proofs:
`Langlands.GroupScheme.connectedGeneration`,
`Langlands.GroupScheme.torusQuotientRationalSurjectivity`,
`unramifiedTorusNeutralFiniteGeneration` and
`Langlands.GroupScheme.torusSurjectionIsogenySection`.
This gives `UnramifiedTorusNeutralSurjectivityStatement.{u}`. The
[neutral-surjectivity assembly](UnramifiedTorusNeutralSurjectivityAssembly.md)
uses connected generation for an open finite-index image between neutral
torus models over the actual Henselian ring `O`.

The local proof `hBound` applies
`unramifiedTorusConnectedBoundAssembly` to
`unramifiedTorusBoundedModel`, `hLift` and
`unramifiedTorusNormPresentation`. It therefore proves
`UnramifiedTorusConnectedBoundStatement.{u}`. The
[connected-bound assembly](UnramifiedTorusConnectedBoundAssembly.md)
extends the generic identity from an arbitrary smooth connected model into
a bounded model and factors it through the relative identity component.
Neutral lifting and the norm presentation place its integral-point image
inside the norm-defined torus Iwahori subgroup.

The local proof `hModel` applies `unramifiedTorusIwahoriModelAssembly` to
`Langlands.GroupScheme.IntegralModel.smoothHomExtension`,
`unramifiedTorusBoundedModel`, `hBound` and
`unramifiedTorusIwahoriConnectedImage`. It proves
`UnramifiedTorusIwahoriModelStatement.{u}`. The
[Iwahori-model assembly](UnramifiedTorusIwahoriModelAssembly.md)
takes the relative identity component of the bounded torus model. The
connected bound gives one inclusion of integral-point images. Extension
and factorization of the connected image model give the reverse inclusion,
so its integral points equal the literal norm-defined Iwahori subgroup
for every supplied finite Galois splitting field.

Finally `unramifiedParahoricModel_of_torusInputs hModel hBound` proves the
exact target. The
[published parahoric construction](UnramifiedParahoricModelConstruction.md)
constructs the compatible full and neutral models on the supplied
apartment from the vertex, bounded-model, intersection and finite-index
results. Its neutral comparison uses the simply connected normalizer
theorem and the two torus inputs. Inner transport moves the actual model
pair and both subgroup identities to the translated apartment, retaining
the original `E.zeroPoints` and the relative component inclusion.

All three local proofs and the final application use the same arbitrary
universe `u`. The entry theorem has no mathematical premises beyond those
already quantified in the target. Its module adds only this proof and
leaves the published target pair and its imports unchanged.
