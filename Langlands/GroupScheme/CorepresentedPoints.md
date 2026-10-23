# Global points of a corepresented affine group scheme

Author: Worker 57.

This module extends the point comparison in `Langlands.GroupScheme.Corepresented`
from affine test schemes to all schemes over an affine base. It constructs a
natural multiplicative equivalence and proves compatibility with the group-scheme
homomorphisms induced by natural transformations.

## Internal provenance and assumptions

This is an internal categorical consequence of the existing corepresentation
adapter and Mathlib's relative global-sections/Spec adjunction
`AlgebraicGeometry.algΓAlgSpecAdjunction`. It makes no additional claim from
external literature. The input is a commutative ring object `R`, a group-valued
functor `F` on commutative `R`-algebras, a representing algebra `B`, and an actual
corepresentation `e : (F ⋙ forget GrpCat).CorepresentableBy B`. The group scheme
is the existing `Corepresented.groupScheme F e`; no output group scheme is
supplied as an additional assumption.

All rings, schemes and group carriers use the same arbitrary universe `u`.
The test scheme `T : Over (Spec R)` is arbitrary: no affineness, reducedness,
nonemptiness or finite-type assumption is added. The `R`-algebra of relative
global sections is `((algΓ R).obj T).unop`. The use of this bundled algebra
retains the structural map to `Spec R` and its induced scalar action.

This module does not construct a particular Deligne splitting, smoothness or
reductivity, or PEL geometry. It supplies the all-test-scheme comparison needed
to use group-valued Yoneda for such later constructions.

## Multiplicative relative adjunction

`adjunctionPointsEquiv F e T` upgrades the relative Spec adjunction to a
multiplicative equivalence

`Hom(algΓ(R)(T), cogroup(F,e).X) ≃* Hom(T, groupScheme(F,e).X)`.

The local instance is exactly the group-object structure on the existing
`cogroup F e`. For multiplicativity, the proof writes the adjunction map as
composition of its unit at `T` with `algSpec.map`. The latter preserves the
multiplication on morphisms because `algSpec` is monoidal. Precomposition with
the unit preserves the multiplication on morphisms into a group object.
The inverse and both inverse identities come from the adjunction itself.

`pointsEquiv F e T` composes the inverse of this multiplicative adjunction with
the existing cogroup point isomorphism. Its codomain is
`F.obj ((algΓ R).obj T).unop`, with the original group law of `F`. Thus the
resulting equivalence refers to the group law on the already constructed
affine group scheme, rather than installing another group law on its points.

`pointsEquiv_apply` identifies its value with `e.homEquiv` applied to the
algebra homomorphism obtained from the relative adjunction, reversing the
opposite-category arrow. This identity is definitional.

## Naturality and induced maps

`pointsEquiv_naturality` states that for every arrow `a : T' ⟶ T` over
`Spec R` and every point `x : T ⟶ groupScheme(F,e).X`, restricting `x` along
`a` corresponds to applying `F.map` to the relative global-sections map
`((algΓ R).map a).unop`. The proof combines naturality of the inverse
adjunction equivalence with the corepresentation's composition law.

`globalPointsFunctor F` bundles this group-valued presheaf as
`(algΓ R).op ⋙ presheaf F`. `globalPointsIso F e` is a natural isomorphism
from `GroupScheme.points (groupScheme F e)` to that presheaf, whose component
at `op T` is `pointsEquiv F e T`. The naturality proof is exactly the previous
restriction identity.

Finally, let `G` be another group-valued algebra functor with corepresentation
`d` by `C`, and let `α : F ⟶ G` be a natural transformation of group-valued
functors. `groupSchemeMap_points` proves that postcomposition with the already
constructed `groupSchemeMap e d α` corresponds to the component of `α` at
the relative global-sections algebra, on every test scheme `T`.

The proof first moves postcomposition through the inverse relative adjunction.
The defining universal-point formula for the algebra map then reduces the
claim to the composition law of `d`, naturality of `α`, and the composition
law of `e` at the identity of `B`. This also explains the order of the two
contravariant algebra maps. All compatibility assertions are proved in Lean.
