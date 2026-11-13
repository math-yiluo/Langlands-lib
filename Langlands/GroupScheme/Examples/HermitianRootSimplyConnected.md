# Simple connectedness of the weighted Hermitian group scheme

This internal module proves that the special unitary group of the weighted Hermitian form,
`HermitianRoot.SchemeModel.groupScheme k L H w hw`, is simply connected. That group is the
actual group scheme of the Hermitian model from
`Langlands.GroupScheme.Examples.HermitianRootGroupScheme`. Simple connectedness is the Library's
`IsSimplyConnected`, which bundles semisimplicity with the condition that every central isogeny
from a semisimple group is an isomorphism.

The hypotheses are exactly those of the Library's splitting isomorphism
`HermitianRoot.SchemeModel.splittingIso`:

- `L / k` is a separable quadratic field extension;
- `Middle` is a finite type with decidable equality;
- `H` is a diagonal Hermitian form on `Middle` for the nontrivial involution of `L / k`;
- `w : Middle → Lˣ` are unit weights, with `hw` saying that `w i` is the weight `H.weight i`.

The group scheme is the fixed subgroup of the weighted inverse-adjoint twist on the Weil
restriction of `SL` over `Index Middle = Unit ⊕ (Middle ⊕ Unit)`. In other words, it is the
special unitary group of the weighted Hermitian form on `Index Middle` built from `H` (see
`HermitianRootGroupScheme`).

## The theorem

* `isSimplyConnected k L H w hw`: `IsSimplyConnected (groupScheme k L H w hw)`.

Proof: after scalar extension to `L`, the group becomes the split special linear group.
`splittingIso k L H w hw` identifies `baseChangeGroupScheme k L H w hw`, the base change along
`Spec L → Spec k`, with `SpecialLinear.groupScheme (Index Middle) (CommRingCat.of L)`. That group
is simply connected by `SpecialLinear.isSimplyConnected` (from
`Langlands.GroupScheme.SpecialLinearSimplyConnected`; `Index Middle` is nonempty).
`IsSimplyConnected.of_iso` transports this to the base change. Finally, the Library's
`IsSimplyConnected.of_algebraicExtension` reflects simple connectedness along the extension
`L / k`. That extension is finite (degree two, `Algebra.IsQuadraticExtension.finrank_eq_two`),
hence algebraic.

## Provenance

This module is internal. It combines the Library's splitting isomorphism with the standard fact
that `SL_n` is simply connected (Milne, *Algebraic Groups* (2017), Example 23.61, printed
p. 502). The special unitary group of a nondegenerate Hermitian form over a separable quadratic
extension is a `k`-form of `SL_n`, where `n` is the cardinality of `Index Middle`, so it is
simply connected too. The theorem allows every finite `Middle`, including the empty type. Then
`Index Middle` has two elements and the group is a `k`-form of `SL_2`, of type `A_1`. This
module makes no claim about inner or outer forms. The proof uses only base change to `L`, not to
an algebraic closure.
