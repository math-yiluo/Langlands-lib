# Inverse-unit rescaling of Weyl-normalized root pairs

This is internal derived content for the local Isomorphism Theorem. It adapts
the published calculation `RingRootCell.WeylData.normalizedWeylPoint_rescale`
to the all-test laws of an actual supplied opposite root pair. The final
application uses `localSplitRootPairLaws`. No new source assertion is made.

Let `R` be an arbitrary commutative local ring, `G` an affine reductive group
scheme, and `i` a closed coordinate split torus maximal on every residue-field
fibre. Let `P` be an actual fibrewise root datum and `a` any of its roots.
Suppose `xp` and `xm` parametrize `P.root a` and its negative, and
`weylPoint xp xm` acts on the torus by `P.reflection a`. For every unit
`kappa` of `R`, the pair

```
scaleHom (kappa : R) ≫ xp,
scaleHom ((kappa⁻¹ : Rˣ) : R) ≫ xm
```

has a Weyl product with the same torus action. The proposition interface is `LocalSplitRootPairRescalingStatement`, proved
by `localSplitRootPairRescaling`. The directly applicable theorem is
`LocalSplitCell.isWeylPoint_rescale`. There is no reducedness, noetherian,
henselian, or characteristic hypothesis, and `a` need not be simple.
The full Isomorphism Theorem is separate.

## The all-test calculation

The generic theorem `LocalSplitCell.RankOneLaws.rescale_relation` works over
any commutative ring, assuming `RankOneLaws i nu xp xm`, negative-root
equivariance for exponent `-alpha`, and `coPairing alpha nu = 2`.
At a scheme test `Z`, write `A(x) = rootPoint xp Z x`,
`B(y) = rootPoint xm Z y`, `H(q) = cocharPoint nu Z q ≫ i.hom.hom`,
and let `n` be the constant restriction of the original Weyl product.
For every global unit `q`, the theorem proves

```
H(q) * (B(-q) * (A(q⁻¹) * B(-q))) = n.
```

Specialize the unit-denominator rank-one law to `x = 1`, `y = q-1`,
and denominator `q`. Negative-root equivariance gives
`H(q) * B(-q) = B(-q⁻¹) * H(q)`, because the negative exponent has
cocharacter pairing minus two. The scalar identity
`-1 + q⁻¹(q-1) = -q⁻¹` and additivity of `B` express the product as

```
B(-1) * (B(q⁻¹(q-1)) * (H(q) * A(q⁻¹))) * B(-q).
```

Substituting the rank-one relation and combining the final negative-root
factors gives `B(-1) * (A(1) * B(-1)) = n`. This calculation never
requires `q-1` to be a unit.

## Preservation of the prescribed action

`LocalSplitCell.RankOneLaws.isWeylPoint_rescale` retains the same generic
hypotheses and additionally assumes the original Weyl product has a
prescribed action `f`. At every test `Z`, take `q` to be the image of
`kappa⁻¹` under the base-scalar ring homomorphism. Restriction and the
formula for `rootPoint` of a scaling map identify the parenthesized
three-factor product above with the restriction of the rescaled Weyl
product `n_kappa`. Thus `H(q) * n_kappa = n`.

Conjugation by `n_kappa` is conjugation by `n` followed by conjugation by
`H(q)⁻¹`. The latter fixes every torus point, including its image under
`f`, because the coordinate split torus is commutative. This proves the
same prescribed torus action on every scheme test.

For the local reductive-group application, `localSplitRootPairLaws`
supplies the generic laws and the actual fibrewise root-coroot pairing
is two. The generic result therefore applies to every root.
