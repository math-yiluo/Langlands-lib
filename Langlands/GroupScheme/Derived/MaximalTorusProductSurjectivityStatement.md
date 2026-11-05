# Surjectivity of derived-subgroup and maximal-torus multiplication

Author: Worker 1554.

`DerivedMaximalTorusProductSurjectivityStatement.{u}` is a proposition
definition. It states a structural result and contains no proof.

For every field `k : Type u`, let `H` and `D` be actual group schemes over
`Spec k`, let `T` be an actual commutative group scheme, and let
`d : D → H` and `i : T → H` be homomorphisms. Assume precisely that `H`
is connected reductive, that `d` is the actual full derived-subgroup
inclusion (`IsDerivedSubgroup d`), and that `i` is a maximal torus
(`IsMaximalTorus i`). Then the conclusion is

```lean
Surjective (subgroupProductMap d i).left
```

The map is the published actual morphism of schemes over `Spec k`:
`D ×_k T → H`, sending `(x,t)` to `d(x) i(t)`, in that order.
The conclusion is surjectivity on underlying scheme points. It does not
assert surjectivity on `k`-rational points or on points of every relative
test scheme. Multiplication need not be a group homomorphism, since the
two images need not commute.

All fields and universes are retained. In particular, there is no
algebraic-closedness, perfectness, splitness or characteristic-zero
premise. A derived subgroup and a maximal torus are supplied, rather
than chosen by an unproved existence construction.

The provenance is internal. This isolates the `D · T = H` structural
step in the prospective proof recorded in the published
`SimplyConnected.DerivedCoverTorusProductSmoothStatement` Markdown.
It is a separate, more general structural obligation: it involves no
simply connected cover and asks for scheme surjectivity rather than
smoothness. One prospective route uses the quotient by the derived
group and the image of a maximal torus; that quotient and image argument
are not implemented or assumed in this module.

For the smoothness consumer, a supplied central cover `π : C → D`
is already surjective as a scheme morphism. Once this statement is proved,
base change of `π` to `D × T` and composition with the displayed product
will give surjectivity of `C × T → H`. Smoothness of the full torus
preimage and the smooth-product argument remain separate proof obligations.
