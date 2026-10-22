# Extending base-field automorphisms

Author: Worker 66.

This proof is an internal derived field-theory result for the published
`Langlands.FieldTheory.AlgClosedAutomorphismExtensionStatement`. It is not
a quotation from the Shimura literature. Its closing theorem is
`Langlands.FieldTheory.algClosedAutomorphismExtension`, with independent
universe levels `uF` and `uOmega` and no additional assumptions.

The proof chooses a transcendence basis `s` of the algebraically closed field
`Ω` over `F`. Algebraic independence identifies the subalgebra `A` generated
by this basis with `MvPolynomial s F` using `AlgebraicIndependent.aevalEquiv`.
Conjugating the coefficientwise automorphism `MvPolynomial.mapEquiv s e`
by this equivalence gives an automorphism `eA` of `A`. On a constant `x`,
this sends `algebraMap F A x` to `algebraMap F A (e x)`.

Mathlib's `IsAlgClosed.isAlgClosure_of_transcendence_basis` shows that `Ω`
is an algebraic closure of `A`. Then `IsAlgClosure.equivOfEquiv Ω Ω eA`
extends `eA` to an automorphism of `Ω`.
`IsAlgClosure.equivOfEquiv_algebraMap`, together with the scalar-tower
identity for `F → A → Ω`, proves the required restriction to `F`.
The original extension `Ω/F` need not be algebraic.

The proof uses the pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` and Lean 4.34.0.
Its two imports are the published target module and
`Mathlib.FieldTheory.IsAlgClosed.Classification`; the target and its
imported dependencies are unchanged.
