# Actual conjugate parabolic data

This internal construction transports an actual semidirect decomposition
`P = M ⋉ U` by an element of the ambient topological group. It constructs the
subgroup `g H g⁻¹` by the literal membership condition
`g⁻¹ * x * g ∈ H`. Closedness and the semidirect decomposition are proved,
not added as hypotheses for the transported data.

The proof of complement transport applies the ambient group isomorphism to the
multiplication bijection. Conjugation then transports the subgroup inclusions
and normalizer inclusion. Closedness is the preimage of the original closed
subgroup under continuous inverse conjugation.

`conjugateSubgroup_eq` identifies this subgroup with any supplied subgroup
having the same literal membership condition.
`IsSemidirectDecomposition.conjugateWithLevi` uses that equality to retain a
specified actual Levi subgroup as its middle argument. Consumers can therefore
compare induction from the conjugated parabolic and another parabolic with
exactly the same Levi type.

The construction is derived from the published generic subgroup and conjugation
interfaces: `IsSemidirectDecomposition` and `conjugationEquiv` in
`Langlands.Representation.Aubert.General.Parabolic`, and Mathlib's
`Subgroup.comap`, `Subgroup.IsComplement'`, and
`Subgroup.le_normalizer_comap`. It is an internal group-theoretic construction;
no original-literature assertion is claimed. It contains no proof of
independence of parabolic induction from the choice of parabolic with a fixed
Levi or of the rational-point Weyl conjugacy target.
