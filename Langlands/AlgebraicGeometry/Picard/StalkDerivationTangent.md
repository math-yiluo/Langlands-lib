# Actual rational tangent maps and actual point-stalk derivations

Let `X` be any scheme over an arbitrary field `K`, with structure morphism `p`
and a specified rational point `x`. The point stalk is the actual
`X.presheaf.stalk (x (IsLocalRing.closedPoint K))`. Its base algebra is
`stalkAlgebraOver p`, and its action on the coefficient field is induced by the
actual rational augmentation `rationalStalkAugmentation p x hx`.

`rationalStalkDerivationTangentEquiv` composes the augmented-algebra
derivation/dual-number equivalence with the actual stalk/tangent-map
equivalence. Its right carrier consists of actual morphisms from
`Spec (DualNumber K)` satisfying both tangent equations, rather than a
replacement tangent carrier.

The forward formula is spectrum of the algebra map
`a ↦ (rationalStalkAugmentation p x hx a, D a)`, followed by `X.fromSpecStalk`.
Zero gives the constant tangent map. Multiplication of `D` by every scalar
`c : K` gives precomposition by spectrum of the actual algebra endomorphism
`epsilonScale c`; the proof uses the algebra scaling formula and
contravariance of spectrum. Injectivity shows that the tangent map is constant
exactly when `D` is zero.

This internal composition uses the two coordinate and stalk constructions
directly. It supplies an equivalence of types and its geometric scalar
formula. It does not identify the sheaf-defined tangent module, assert a
linear equivalence to that module, or compare with cohomology.
