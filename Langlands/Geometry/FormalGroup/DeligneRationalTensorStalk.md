# Tensor products and the actual rational stalk

This derived module constructs the canonical tensor/stalk comparison for
the existing rationalization of an actual module sheaf. It identifies the
existing integral-to-rational stalk map with the actual tensor unit.

The source motivation is Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), Section 2 A, printed pp.109–110 (PDF pp.3–4): the rational frame
in item 4 and the determinant lattices in condition (c). Registered source:
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The comparison and its compatibility results are derived infrastructure;
they are not separate assertions quoted from the paper.

## Parameters and construction

Let `O` be a commutative ring, `F` an `O`-algebra field, `X` a
topological space, `M` an actual sheaf of `O`-modules, and `x` a point
of `X`. Rings, spaces and module carriers are in the common universe `u`.
There is no fraction-field, flatness, locality, or nilpotence assumption.

The existing `rationalSheafFunctor F X` first extends coefficients on
sections and then sheafifies in `F`-modules. The actual stalk is the
colimit over open neighborhoods of `x`. Scalar extension is a left
adjoint, so it preserves this colimit. The categorical sheafification
unit induces an isomorphism on actual stalks.

`rationalTensorStalkIso` composes the colimit comparison
with the stalk of that sheafification unit. Its source is the actual
module obtained by extending scalars of `M_x`, and its target is the
actual stalk `(rationalSheafFunctor F X M)_x`. Thus its source is
`F tensor_O M_x` with the `F`-module structure. No arbitrary tensor
presentation or comparison is supplied as input.

## Compatibility with germs and the integral map

`rationalTensorStalkIso_germ` computes the comparison after extending
each actual germ: it is the sectionwise sheafification unit followed by
the actual target germ. Its proof uses the defining identity of the
colimit comparison and naturality of germs under the sheafification
map. `rationalTensorStalkIso_tmul_germ` evaluates this equality on every
pure tensor `a tensor m`.

`rationalTensorStalkIso_unit` proves that the tensor unit on the integral
stalk, followed by the scalar restriction of this comparison, equals
the existing `integralRationalStalkMap`. It compares the maps on all
germs, applies naturality of the extension/restriction adjunction unit,
and uses the preceding germ computation and the existing germ formula
for the integral map.

`rationalTensorStalkIso_one_tmul` evaluates that equality on any integral
stalk element. Thus the integral map is precisely `m ↦ 1 tensor m`
through this constructed comparison.

`rationalTensorStalkIso_naturality` states the naturality square for
every actual `O`-linear sheaf map. The proof tests the two `F`-linear
maps on tensors `1 tensor m`, uses the preceding formula, and applies
the existing naturality of the integral-to-rational stalk map.

## Scope

This supplies the tensor/stalk comparison for the existing rational
sheaf and integral map, including their naturality. It does not prove
injectivity of that integral map, an exterior-power subsheaf comparison,
or equivalence of the existing admissibility predicate with the full
source moduli interpretation. It constructs no projective linear
action, special formal module comparison, or representing formal scheme.
