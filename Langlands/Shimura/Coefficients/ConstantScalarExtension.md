# Scalar extension of constant-module associated sheaves

This internal categorical construction extends `ScalarExtension` using the
actual sheafified constant-module coefficients from `Associated`. The first
part works on an arbitrary Grothendieck site with actual sheafification for
both commutative module categories. Site object and morphism universes are
independent; rings, module carriers and the group share universe `u`.

`constantExtendScalarsIso` identifies the sheafified tensor extension of a
constant `R`-module sheaf with the constant sheaf of its tensor-extended
`S`-module. Module tensor extension is a left adjoint, so Mathlib proves it
preserves sheafification. Whiskering
`presheafToSheafCompComposeAndSheafifyIso` by the constant-presheaf functor,
then using `compConstIso`, constructs the comparison. This does not require
tensor postcomposition to preserve sheaves before sheafification.

`constantActionExtendScalarsIso` transports this natural isomorphism to
coefficient group actions through `mapActionComp` and `mapActionCongr`. Its
underlying forward and inverse morphisms are the constant-sheaf comparison
components, as the two component lemmas prove.

For an actual scheme `X` and an action `Y` on an object of its small etale
site, `constantAssociatedExtendScalarsComparison` first applies the existing
adjoint associated-sheaf scalar-extension comparison to the constant-module
action. It then applies the associated functor to the constant-action tensor
isomorphism. This is a natural morphism from scalar extension of the
associated `R`-coefficient sheaf to the associated sheaf of the actual tensor
extension of the module representation. Scheme, rings, module carriers and
group use universe `u` in this specialization.

The unit equation states that precomposing the restricted comparison with the
tensor-sheaf unit gives the constructed associated unit followed by the
restricted associated constant-action comparison. It follows from functoriality
and the original adjoint unit equation. The unit-and-inclusion equation
identifies the resulting map into product sections with the original invariant
inclusion followed by the product-section map of the tensor-sheaf unit and
constant-extension coefficient comparison. Its proof uses the unit equation,
`inclusion_natural`, `associatedExtensionUnit_inclusion`, and the underlying
action-component formula.

No finiteness, flatness or torsor premise is required for this canonical
morphism. Its invertibility, tensor-invariant commutation, coefficient-level
reduction coherence and the geometric Harris specialization remain separate
obligations. The constant-sheaf comparison itself is an isomorphism; this does
not imply that the associated-sheaf comparison is invertible.
