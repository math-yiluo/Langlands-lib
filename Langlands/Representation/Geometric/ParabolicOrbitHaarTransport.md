# Actual orbit kernel transport for Haar characters

This internal construction removes only subgroup inclusions from the actual
orbit kernels. The target radical inside its parabolic is continuously
isomorphic to its ambient matrix subgroup, using the published
`BlockShape.unipotentRadicalAmbientEquiv` from
`Langlands.Representation.Parabolic.UnipotentFiniteContainment`.
The constructions use that equivalence directly; the
`parabolicOrbitRadicalAmbientEquiv_apply` lemma records its underlying matrix.
The radical intersection with the
actual orbit stabilizer is continuously isomorphic to the literal ambient
correction subgroup `V ∩ w P w⁻¹`. Composing with the published restricted
retraction equivalences gives the corresponding maps for the actual nested
kernel and intersection. Every map keeps the underlying matrix unchanged.

`haarChar_eq_of_conjugacy` proves that any continuous group isomorphism
intertwining two group automorphisms identifies their actual Haar scaling
characters. Its proof pushes a regular Haar measure across the isomorphism,
transports the source scaling identity, and uses Haar scalar-factor uniqueness
on the target. It assumes no finite total Haar mass.

The subgroup maps require only a commutative topological ring. This module is
an internal derivation from the actual subgroup definitions and the published
restricted kernel equivalences. It claims no normalization cancellation or
final orbit comparison.
