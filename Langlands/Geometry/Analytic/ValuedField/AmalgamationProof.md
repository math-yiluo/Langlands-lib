# Isometric amalgamation of complete ultrametric fields

`Langlands.Analytic.completeFieldAmalgamation` proves the published
`CompleteFieldAmalgamationStatement` at every universe `u`. Two isometric
bounded `K`-algebra maps from a complete ultrametric field `E` to complete
ultrametric fields `F` and `G` admit commuting isometric bounded
`K`-algebra maps into one complete ultrametric field `L : Type u`.
The theorem has no additional hypotheses.

The helper `tensorSeminormStatement` proves the published
`TensorSeminormStatement` by applying
`exists_ultrametricTensorSeminorm` to its chosen field and algebra
structures. That imported theorem constructs the normalized
nonarchimedean projective tensor seminorm. Its hypotheses require neither
completeness nor ultrametricity of the base field, so the complete-field
interface supplies every required instance.

The helper `completeFieldAmalgamation_of_tensorSeminorm` carries out
the following assembly from the tensor, domination and realization
interfaces. The final theorem supplies their published proofs
`tensorSeminormStatement`, `BanachSpectrum.nonarchimedeanDomination`
and `seminormRealization`.

Given complete ultrametric normed fields `E`, `F` and `G` over `K`,
the input isometric maps `i : E → F` and `j : E → G` define algebra
structures over `E` on the two target fields. Their isometry gives
`NormedAlgebra E F` and `NormedAlgebra E G`. The tensor-seminorm
interface supplies a normalized nonarchimedean ring seminorm `p`
on the algebraic tensor product `F ⊗[E] G`, with the specified upper
bounds on both factor inclusions.

Domination gives a normalized multiplicative seminorm `q ≤ p`.
Realization gives a complete ultrametric normed field `L : Type u`
and a ring map from this tensor product to `L` recovering `q`
exactly. The induced factor maps are contractive. The private helper
`norm_eq_of_contracting_ringHom` packages the pulled-back target norm
as a `BanachSpectrum` point of the source field and invokes the
published `BanachSpectrum.field_apply`. This is the field-element
and inverse argument that turns contractivity into exact norm equality.

The factor maps agree on `E` by the tensor relation. The left factor
map defines the `K`-algebra structure on `L`; its exact norm equality
gives the `NormedAlgebra K L` instance. Agreement on `E` and the input
maps' coefficient compatibility show that the right factor map respects
the same coefficient structure. The two ring maps therefore package
as bounded `K`-algebra maps. Pointwise agreement proves the required
equality of bounded algebra maps, and exact norm equality gives both
isometries.

No tensor completion or ambient norm on the tensor product is used.
All carriers stay in `Type u`, including `u = 0`. Trivially valued fields
are included; the argument uses no algebraic closure, nontrivial valuation,
algebraicity, local compactness or spherical completeness assumption.

This is an internal derivation from the imported tensor, domination and
seminorm-realization results and Mathlib's algebraic tensor product. The
tensor construction and its explanation are in `ValuedField.TensorSeminorm`;
the domination and realization arguments are in
`Spectrum.NonarchimedeanDominationProof` and
`ValuedField.SeminormRealizationProof`. The proof implements the common-field
route described in the published
`notes/analytic/valued-field-amalgamation-sources.md`, using the algebraic
tensor directly. This module proves field amalgamation; its application to
compatible affinoid points is a separate theorem.
