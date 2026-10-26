# Scalar restriction of constant-module associated sheaves

This internal categorical construction extends `Associated` and
`ScalarRestriction`. Its inputs are a category `C` with binary products, a
Grothendieck topology `J`, commutative rings `R`, `S`, a ring homomorphism
`φ : R →+* S`, actual sheafification instances for both module categories, a
group `G`, and an object `Y` of `C` with a `G`-action. The site object and
morphism universes are independent; rings, module carriers and the group share
universe `u`.

`constantRestrictScalarsIso` identifies restriction of the actual sheafified
constant `S`-module sheaf with the constant sheaf of its restricted `R`-module.
The construction uses Mathlib's `constantCommuteCompose`. Its preservation of
sheafification hypothesis is proved by the existing adjunction: module scalar
restriction is a left adjoint to coextension. Its preservation of sheaves also
follows from being a right adjoint to tensor extension. No constant-sheaf
comparison is supplied as an additional input.

`constantActionRestrictScalarsIso` transports that natural isomorphism through
`Functor.mapActionComp` and `Functor.mapActionCongr`. It therefore commutes with
every coefficient group operator and is natural in equivariant module maps.
The two underlying-morphism lemmas identify its forward and inverse maps with
the constant-sheaf comparison components.

`constantAssociatedRestrictScalarsIso` composes the associated invariant-limit
restriction isomorphism, evaluated on constant-module actions, with the
associated functor applied to the constant-action comparison. It is a natural
isomorphism from restriction of the associated `S`-coefficient sheaf to the
associated sheaf of the restricted module action. The two inclusion equations
state that its forward and inverse maps carry the actual invariant inclusions
to one another, with the corresponding constant-sheaf coefficient comparison
on product sections. Their proofs use `inclusion_natural`, the respective
`associatedRestrictScalarsIso` inclusion equations, and the underlying-action
component formulas.

No finiteness, flatness, torsor or terminal-object premise is required. This
unit constructs scalar restriction for constant-module coefficients. Scalar
extension and reduction comparisons and the geometric Harris specialization
remain separate constructions; no tensor-invariant commutation is asserted.
