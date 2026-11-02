# Actual point fibres after an isomorphism of atlas objects

This is an internal construction from `PseudofunctorPointFiber` and the
naturality of the pseudofunctor composition comparison. It uses no new
literature assertion.

For a category-valued pseudofunctor `F`, two objects `ξ, ξ'` over the same
atlas object `U`, an actual isomorphism `e : ξ ≅ ξ'`, and a test object `η`
over `T`, `mapPoints` preserves the actual map `a : Z → U` and sends the
actual isomorphism `d : a*ξ ≅ p*η` to `(a*e)⁻¹ ≪≫ d`.

`mapPoints_restrict` proves compatibility with every morphism in `Over T`.
Its proof expands coherent pullback and uses naturality of the composition
comparison at `e.inv`. `mapPoints_symm` cancels the pulled-back isomorphism
with its inverse. `pointsEquiv` therefore gives equivalences on every point
type, and `presheafIso` assembles them into a natural isomorphism of the
entire point-fibre presheaves. All object and morphism universes are arbitrary.

This construction retains actual isomorphisms and takes no isomorphism
classes. It asserts neither existence of a representing scheme nor of an
atlas. The isomorphism `e` is explicit input; constructing it in a geometric
application remains an obligation of that application.
