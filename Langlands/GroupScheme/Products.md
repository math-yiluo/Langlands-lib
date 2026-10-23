# Points of finite products of group schemes

This is an internal categorical derivation from the Library's
`Langlands.AbelianScheme.GroupScheme` and Mathlib's limits of group objects.
It provides the product point API needed to realize the Harris complex group
splitting as a comparison with an actual product of group schemes. No Harris
input or representability hypothesis is needed for this generic prerequisite.

## Binary products

For a base scheme `S : Scheme.{u}` and group schemes `G,H` over `S`,
`productPointsEquiv G H T` identifies

\[
\operatorname{Hom}_S(T,(G\otimes H).X)
\simeq
\operatorname{Hom}_S(T,G.X)\times\operatorname{Hom}_S(T,H.X).
\]

Here the tensor symbol denotes the Cartesian monoidal product of group objects
in `Over S`, and every Hom group uses the actual scheme group law. The map takes
a point to its composites with the two Cartesian projections. The inverse is
the universal pairing map from Mathlib's `homEquivToProd`. Multiplicativity
follows because both projections are monoid morphisms (`MonObj.mul_comp`).
The `_fst` and `_snd` lemmas record the forward formulas;
`productPointsEquiv_naturality` proves compatibility with precomposition by
every test-scheme map using associativity.

This is the same binary construction previously used locally in
`Langlands.Shimura.DeligneTorus.productPointsEquiv`, now available in the generic
`Langlands.GroupScheme` namespace without importing the Deligne torus.
The Deligne-torus module imports this module and retains its existing name as
a definitionally equal compatibility wrapper, so both APIs share this one
implementation.

## Finite categorical products

Let `I : Type u` be finite and `G : I → GroupScheme S`. No enumeration,
inhabitedness, or commutativity of the groups is required. The index and base
scheme use the same universe. `GroupScheme.pi G` is the chosen categorical
product `∏ᶜ G` in the category of group schemes. Scheme finite limits and their
creation by `Grp.forget` provide this product with its actual group structure.

`piIsLimit G` proves that the fan on its underlying object with projections
`(Pi.π G i).hom.hom` is a limit fan in `Over S`. It applies Mathlib's
`isLimitOfHasProductOfPreservesLimit` to the forgetful functor from group
objects. Thus the underlying universal property is obtained from the actual
categorical product; it is not supplied as extra data.

`piPointsEquiv G T` is the multiplicative equivalence

\[
\operatorname{Hom}_S(T,(\textstyle\prod_i G_i).X)
\simeq
\prod_{i:I}\operatorname{Hom}_S(T,G_i.X).
\]

Its forward map is composition with each product projection. Its inverse is
`Fan.IsLimit.lift (piIsLimit G)` applied to the family of points. The factorization
law proves the right inverse, and the same law together with uniqueness of
maps into a limiting fan proves the left inverse. Multiplication is preserved
coordinatewise because each projection is a group-scheme homomorphism.

`piPointsEquiv_apply` and `piPointsEquiv_symm_π` describe these maps on each
coordinate. `piPointsEquiv_naturality` proves that precomposition with
`a : T' ⟶ T` acts on every component by precomposition with `a`. This follows
from associativity of scheme maps. These constructions include the empty
indexing type, where the product is the terminal group scheme and the family
of points has one element.

## Point presheaves and scope

`familyPoints G` is the group-valued presheaf on all schemes over `S` whose
value at `T` is the family of Hom groups above. Its restriction maps are
componentwise precomposition; the group-homomorphism and functor laws follow
from the actual point group laws and categorical identity and associativity.
`piPointsIso G` packages `piPointsEquiv` as an isomorphism from
`GroupScheme.points (pi G)` to `familyPoints G`; its naturality is exactly the
proved pointwise identity.

Test schemes are arbitrary, including nonaffine and empty schemes. This module
constructs the finite-product point comparison only. It does not supply a
general-linear group scheme, the Harris scheme comparison, or assertions of
smoothness or reductivity.
