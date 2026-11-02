# Tensor reassociation for affine relation coactions

This is an internal algebraic construction for the unchanged ring-valued
`GroupoidCoaction` interface. Let `B` and `C` be commutative rings in the
same universe, let the source map be the given `B`-algebra structure on `C`,
and let `t : B →+* C` be any ring homomorphism. The module `M` may be in a
different universe. No equivalence-relation or flatness hypothesis is used.

`TargetRing t` is a separate copy of `C` whose `B`-algebra structure is `t`.
`TargetModule t M` is a copy of the source tensor product `C ⊗[B] M`,
with its `B`-module structure restricted along `t` on the coefficient factor.
`targetLinearMap` expresses a coaction as an ordinary `B`-linear map into
this module.

`PairRing t` is a separate copy of `C ⊗[B] TargetRing t`. Its final
`B`-algebra structure comes from the source map into the second factor.
`pairFirst` and `pairSecond` are the inclusions of the two copies of `C`;
`pair_compat` proves that source on the first factor equals target on the
second factor.

The additive map `pairTensorMap t M` sends
`c ⊗ (c' ⊗ m)` to `(c ⊗ c') ⊗ m`, with these specified scalar structures.
The separately constructed additive map `pairTensorInv t M` sends the latter
pure tensor to the former. Both maps use two applications of the balanced
additive tensor lift. `pairTensorInv_pairTensorMap` proves that the second
map is a left inverse, by induction on each tensor product. Thus
`pairTensorMap_injective` proves injectivity. Only this direction of the
inverse identity is asserted. The lemmas with suffix `_tmul` record the
pure-tensor formulas.

These definitions and their elementary proofs are derived directly from
balanced tensor products. They are supporting algebra for coherent cores;
this module makes no coherent-exhaustion or nonzero-invariant claim.
