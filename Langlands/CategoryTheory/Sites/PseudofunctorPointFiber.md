# Actual point fibres of a category-valued pseudofunctor

For a category `C` and a contravariant Cat-valued pseudofunctor `F`, fix
objects `ξ` over `U` and `η` over `T`. This module constructs a presheaf on
`Over T`. Its value at `p : Z → T` consists of a map `a : Z → U` and an
actual isomorphism

`a* ξ ≅ p* η`.

The isomorphism is retained as data. It is neither a proposition that such
an isomorphism exists nor an equality of isomorphism classes. This is the
set-valued point-fibre construction needed when asking whether a scheme
mapping to a groupoid-valued pseudofunctor has representable base changes.
No representability, sheaf property, stack property or atlas is asserted.

`pullIso` pulls back an isomorphism along `g : Y' → Y`. It uses the
pseudofunctor's composition comparison to identify pullback along each
specified composite with iterated pullback. Its forward morphism is
exactly Mathlib's `Pseudofunctor.LocallyDiscreteOpToCat.pullHom`. Equality
of forward morphisms of isomorphisms therefore gives the identity and
composition laws from the corresponding published `pullHom` laws.

`Points` is the dependent pair of the map and isomorphism above.
`restrict` sends `(a, e)` along `q : Z' → Z` over `T` to
`(q ≫ a, pullIso e q (q ≫ a) p')`, where `p' : Z' → T` is the structure
map. The equation that `q` lies over `T` supplies the second composition
comparison. The identity and composition laws prove that these maps
define `presheaf` on the entire slice category.

`projection` forgets the isomorphism and retains the map `a`, with a
universe lift. Its target is the restriction of the lifted Yoneda
presheaf of `U` along `Over.forget T`. The component formula commutes with
precomposition and hence is natural.

The base-category morphisms may live in universe `v` and the fibre
category morphisms in universe `v'`; the resulting presheaf takes values
in `Type (max v v')`. The object universe of the fibres is independent.
No topology, size finiteness, groupoid or geometric assumption is needed
for these constructions.

The provenance is internal and derived. The implementation specializes
the composition comparisons and `pullHom` laws in pinned Mathlib's
`CategoryTheory/Sites/Descent/IsPrestack.lean`, and uses ordinary
isomorphism extensionality, dependent pairs and the lifted Yoneda functor.
It introduces no assertion from external literature. Applying this
construction to a Picard groupoid, proving geometric representability
and constructing a smooth atlas remain separate obligations.
