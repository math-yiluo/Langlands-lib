# Field extension on all actual component groups

Author: Worker 1107.

Let `k` and `L` be algebraically closed fields in the same arbitrary universe
`u`, let `φ : k →+* L` be a field homomorphism, and let `H` be an actual smooth
affine group scheme over `Spec k`. Write `H_L` for the actual pullback along
`specMap φ : Spec L → Spec k`. Characteristic is unrestricted, and no
algebraicity, separability or finite-dimensionality assumption is made on
the extension.

`allComponentBaseChange H φ` is a homomorphism from
`AlgebraicallyClosedComponents H` to `AlgebraicallyClosedComponents H_L`.
These are the published finite groups whose carriers are all connected
components of the actual underlying schemes. The construction composes the
inverse of `allComponentQuotientEquiv H`, the published
`rationalComponentBaseChange H φ`, and `allComponentQuotientEquiv H_L`.
Thus it uses the ordinary quotient groups of rational sections to construct
a homomorphism on all actual scheme components.

`allComponentBaseChange_quotient` is the resulting comparison equation for
each ordinary rational-component class. The proof cancels the source
comparison equivalence and its inverse. `allComponentBaseChange_ofPoint`
says that a component represented by a rational section is sent to the
component of its actual pulled-back section. Its proof applies the quotient
comparison equation and the published representative equation for
`rationalComponentBaseChange`. Since every source component has a rational
representative, this formula determines the homomorphism uniquely and is
independent of the chosen representative.

`allComponentBaseChange_fst` proves that the continuous first projection
`H_L → H` sends the extended component back to its original component.
Surjectivity of the source quotient comparison reduces the equation to the
published `rationalComponentEmbedding_baseChange`. The projection on actual
components is therefore a left inverse of the constructed homomorphism.
Applying it to an equality after extension proves
`allComponentBaseChange_injective`.
`componentProjection_surjective_of_isAlgClosed` also follows: the constructed
extension of any source component is an explicit preimage under projection.
This last theorem concerns surjectivity of the projection from the changed
scheme's components to the original scheme's components.

For an actual group-scheme homomorphism `f : H ⟶ H'`, with `H'` smooth affine
over `k`, `allComponentMap_quotient` identifies the published full-component
map with the published ordinary quotient map under their comparisons.
The proof uses the actual continuous component-map formula and
`rationalComponentEmbedding_naturality`. Using that equation,
`allComponentBaseChange_naturality` proves equality of the two homomorphisms
obtained by first extending the field and then applying the actual pullback
of `f`, or first applying `f` and then extending the field. The source
comparison's surjectivity reduces this to the already published naturality
of `rationalComponentBaseChange`.

This is an internal derived construction from the published
`AlgebraicallyClosedComponents` and `IdentityComponentRationalBaseChange`
interfaces; the latter is imported through the former's existing imports.
No external structure theorem or additional component-rationality premise
is introduced. The paragraphs above describe the implemented Lean proofs.

Surjectivity of `allComponentBaseChange`, an inverse group homomorphism,
comparison between different algebraically closed extensions, and an
extension-independent geometric component group remain separate structural
obligations. The construction introduces no component-group scheme,
sheaf quotient, or descent of fixed components to rational points.
