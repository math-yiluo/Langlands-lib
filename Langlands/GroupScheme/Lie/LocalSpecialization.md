# Differential surjectivity from the local special fibre

For a homomorphism `f : G ⟶ H` of affine group schemes over `Spec R`,
`HasSurjectiveDifferential f A` means that the specified homomorphism induces
a surjective map on the actual dual-number Lie modules with coefficients
in the commutative `R`-algebra `A`. It uses `targetMapLinear f A`, rather
than an unspecified linear map between abstract modules.

The main theorem `hasSurjectiveDifferential_of_specialFibreIso` assumes
that `R` is a commutative local ring, that both group schemes are smooth
and affine, and that the pullback of `f` to `R / maximalIdeal R` is an
isomorphism. It proves `HasSurjectiveDifferential f A` for every
commutative `R`-algebra `A` in the same universe. There is no field,
noetherian, reductivity, henselianity or isogeny hypothesis. The conclusion
asserts differential surjectivity; it does not assert that `f` is an
isomorphism or that its full kernel is trivial.

The proof first transfers differential surjectivity of the special-fibre
isomorphism through the published actual Lie base-change equivalences.
The naturality theorem
`targetMapLinear_smoothKernelScalarExtension` then expresses that
residue-field differential as the scalar extension of the differential
over `R`. Smoothness makes the target Lie module finite. The auxiliary
lemma `surjective_of_lTensor_residueField_surjective` uses the
residue-field version of Nakayama's lemma from Mathlib to deduce
surjectivity over `R`. Finally,
`targetMapLinear_surjective_of_base` extends surjectivity to `A` through
the published smooth Lie scalar-extension equivalences. Naturality is
proved on simple tensors and extended by tensor induction.

This is an internal consequence of the published actual Lie constructions
in `Lie.SmoothScalarExtension`, `Lie.LinearBaseChangeNaturality` and
`Lie.SmoothDifferential`, together with Mathlib's local-ring module
theory. It supplies a differential step for the prescribed-map rigidity
argument in the fibrewise-isogeny task; it does not claim the remaining
centrality or finiteness steps of that argument.
