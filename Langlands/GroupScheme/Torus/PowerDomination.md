# A dense map from a finite power of a torus gives one from a torus

Worker 1143.

This module proves a small step in the torus-domination argument for connected
reductive groups: if some finite power of a torus maps to a scheme with dense
image, then a single torus does. It is an internal consequence of published
definitions. These are `finitePower` from `ImageGenerationProducts.lean`, the
group-scheme product `GroupScheme.pi` and its point description
`piPointsEquiv` from `Products.lean`, and the torus predicate `IsTorus` from
`Torus/Lattice.lean`. It also uses `IsTorus.pi` from `Torus/Products.lean`.

The step has no numbered counterpart in the literature. It is the last part
of the derivation recorded in `Reductive/TorusDominationStatement.md`. The
proof of Corollary 17.92 in J. S. Milne, *Algebraic Groups* (2017), printed
p.382, uses "a dominant morphism `C_1 × ⋯ × C_m → G`" from a finite product of
Cartan subgroups. For a connected reductive group these are tori, and the
product is combined into one torus. Here the source of the dominant map is
the `n`-th power of one torus `P`.

## Two morphisms between the products

Let `P` be a group scheme over an arbitrary base scheme `B`, and let `n` be a
natural number. There are two products with `n` factors equal to the
underlying scheme `P.X`:

- the scheme-level power `finitePower P.X n`, the categorical product in
  `Over B` indexed by `Fin n`;
- the underlying scheme of the group-scheme product
  `GroupScheme.pi (fun _ : ULift (Fin n) => P)`, the categorical product in
  `GroupScheme B` indexed by `ULift (Fin n)`. The index is lifted to universe
  `u` because `GroupScheme.pi` takes index types in the universe of the base.

The module gives morphisms in both directions:

- `piFinitePowerHom P n` goes from the group-scheme product to
  `finitePower P.X n`. It is the product lift of the underlying morphisms of
  the group-scheme projections.
- `finitePowerPiHom P n` goes from `finitePower P.X n` to the group-scheme
  product. It is the inverse of `piPointsEquiv`, applied to the family of
  projections of `finitePower P.X n`.
- `finitePowerPiHom_comp`: `finitePowerPiHom P n ≫ piFinitePowerHom P n` is
  the identity of `finitePower P.X n`. Both sides agree after each projection,
  by `Pi.lift_comp_π` and `piPointsEquiv_symm_π`, so `Pi.hom_ext` gives the
  equation.

The module does not show that the two morphisms are inverse isomorphisms; the
section property is all that the density argument needs.

## Density

`exists_isTorus_dense_of_finitePower` works over `Spec k` for a field `k`.
Its hypotheses are a torus `P`, a natural number `n`, a scheme `X` over
`Spec k`, and a morphism `g : finitePower P.X n ⟶ X` whose underlying map of
topological spaces has dense range. It concludes that there are a group scheme
`T` and a morphism `f : T.X ⟶ X` such that `T` is a torus and the range of
`f` is dense.

The proof takes `T` to be the group-scheme product of `n` copies of `P`. It is
a torus by `IsTorus.pi`, since `ULift (Fin n)` is finite. It takes
`f = piFinitePowerHom P n ≫ g`. Every point `g x` of the range of `g` is also
`f` applied to `finitePowerPiHom P n x`, by `finitePowerPiHom_comp`. So the
range of `f` contains the range of `g`, and a set containing a dense set is
dense.

No group structure on `X` and no hypothesis on `k` is used. The theorem does
not say that `f` is a homomorphism, and it does not compute the rank of `T`.
