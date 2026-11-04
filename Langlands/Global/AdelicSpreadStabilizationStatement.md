# Eventual stabilization of arithmetic stages

This statement formalizes the eventual equality in Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.11,
Proposition 4.4. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Theorem 3.4 and Remark 3.5, pp.5–6, and the section 4 construction on p.9
justify using any supplied finite-type arithmetic spread.

For a proper scheme `Y` over the original global field, a finite-type model
`X` over the outside-`S` integers and a specified generic-fibre isomorphism
`e`, there is a finite superlevel `T` such that, for every `U` containing `T`,
the actual map from the `U`-stage to `Y`'s full adelic points is a
homeomorphism. The map first changes the point's coefficient ring along
the literal inclusion into the full adele ring and then applies the
generic-fibre point equivalence associated with `e`.

The domain is written over the fixed initial integer base. Its
`fixedModelStageTopology` is transported by `fixedModelPointHomeomorph`
from the original topology on points of the actual pullback of `X` to
the `U`-integers. Thus it is precisely the arithmetic stage in the source.
The target has the explicit `spreadAdelePointTopology` defined from `X`
and `e`. The homeomorphism formulation records the topology implicit in
the source's equality: the arithmetic stage map is continuous and open,
and becomes bijective at every sufficiently large level.

No separatedness or properness is assumed for the initial arithmetic
model. Properness of `Y` implies separatedness of the generic fibre;
eventual separatedness of the supplied model provides eventual
injectivity. Compactness and the directed open cover by arithmetic
stages give eventual surjectivity. These explain the derived topological
form of the source assertion; this file states the result and does not
prove it.

Both clauses retain nonaffine schemes and arbitrary initial finite
levels, including the empty level. In the function-field clause the
constant field is finite, the rational-function action has the specified
compatible scalar tower, and `FunctionField` imposes finite
dimensionality without imposing separability. Nonempty superlevels are
cofinal, so an empty initial function-field level causes no restriction.
The number-field clause includes all infinite completions as well as
all finite places. The two clauses share an arbitrary universe `u`.
