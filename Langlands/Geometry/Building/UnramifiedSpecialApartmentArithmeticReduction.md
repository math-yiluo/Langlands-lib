# Arithmetic reduction for ordinary special-apartment chambers

Authors: Worker 198 and Worker 352.

This derived reduction proves that the existing
`Langlands.GroupScheme.ConnectedGenerationStatement.{u}` implies
`UnramifiedSpecialApartmentChamberStatement.{u}`, at arbitrary universe `u`.
The entry proposition is
`UnramifiedSpecialApartmentArithmeticReductionStatement`. Its proof is
`unramifiedSpecialApartmentChamber_of_connectedGeneration`. The conclusion is
the existing chamber proposition itself, with unchanged hypotheses, every field
and residue characteristic, ordinary affine roots, and the supplied apartment
throughout. Connected generation remains an explicit premise; this unit is not
an unconditional proof of the chamber proposition.

The helper `unramifiedSpecialApartmentChamber_of_arithmetic` first proves the
chamber conclusion from three explicit arithmetic propositions:
`UnramifiedTorusConnectedBoundStatement`,
`UnramifiedZeroFixerSharpComparisonStatement`, and
`UnramifiedRootPositiveReductionStatement`.

The proof first constructs the torus Iwahori model proposition from the connected
bound, the published smooth homomorphism-extension theorem, the maximal bounded
integral-model theorem and the connected-image theorem. The bounded torus model
is supplied by `unramifiedTorusBoundedModelAssembly`. Thus no additional torus
model-existence proposition is retained as an input.

For each instance of the chamber proposition,
`unramifiedGaloisFixedApartment` supplies an initial point in the given apartment
fixed by the actual coefficient action. Apartment extensionality identifies this
with fixedness under the affine action. The published
`recoveredFixedPointModels` constructs actual lower and upper relative component
models and their compatible recovery for this singleton. The zero datum is
chosen using `UnramifiedZeroDatum.ofConnectedReductive`, applied to the
connected reductive group after algebraic extension.

The building datum `B` is `MaximalUnramified.buildingDataOfApartment`, using
exactly the given apartment, centralizer, and integer-valued omega compatibility.
Consequently the recovered model's full integral-point equality is the full
norm-one fixer equality for `B`. A singleton is nonempty, and its image under
each real affine function is finite and bounded above. The sharp-comparison
premise therefore applies. The neutral/zero-fixer assembly, using that
comparison and the two torus propositions already obtained, identifies the
entire upper neutral integral-point subgroup with the zero-subgroup point
fixer. This is a global subgroup equality.

Finally, `exists_regular_galois_stable_facet_of_recoveredModels` uses these
models, the zero datum, this entire neutral-fixer equality, positive root
reduction and the initial fixed point. It supplies a regular point for the
ordinary affine-root arrangement in the same apartment and setwise equality of
the image of its whole sign facet under every coefficient automorphism.

The final theorem discharges these three arithmetic inputs, conditional only on
connected generation. It applies
`unramifiedTorusNeutralSurjectivityAssembly` to connected generation and the
published torus-quotient rational-surjectivity, neutral finite-generation and
surjection isogeny-section proofs. This gives neutral lifting. The published
bounded torus model, this neutral lifting, and the published torus norm
presentation give the connected bound through
`unramifiedTorusConnectedBoundAssembly`. The other two inputs are the
unconditional published `unramifiedZeroFixerSharpComparison` and
`unramifiedRootPositiveReduction`.

All constructions and implications are compositions of the named Library
results. This unit asserts no additional literature theorem, changes none of
the input statements, and does not prove connected generation. It uses no local
anisotropic classification, local rank-one classification or local Kneser–Tits
input.
