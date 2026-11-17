# Uniqueness of Weyl-normalized root partners

This is internal derived content for the local Isomorphism Theorem. It uses the
published all-test rank-one laws, scalar rigidity of root parametrizations,
the actual relative cocharacter centralizer, and self-centralization of a
fibrewise maximal torus. It introduces no new source assertion.

For a commutative local ring `R`, let `G` be an affine reductive group scheme,
`i` a closed coordinate split torus that is maximal on every residue-field
fibre, and `P` an actual fibrewise root datum. Fix any root `a` and a root
parametrization `xp` of `P.root a`. If `xm` and `xm'` both parametrize the
opposite root and both products `weylPoint xp xm` and `weylPoint xp xm'`
act on the torus by `P.reflection a`, then `xm' = xm`.

The proposition interface is `LocalSplitRootPartnerUniquenessStatement`,
proved by `localSplitRootPartnerUniqueness`. The directly applicable theorem is
`LocalSplitCell.rootPartner_unique`. The theorem
`splitTorus.RelativeCocharacterCentralizer.rootPartner_unique_of_isolating_cocharacter`
proves the same conclusion when an isolating cocharacter is supplied.
The ring is not required to be reduced, noetherian, or henselian, and there
is no characteristic restriction. The full Isomorphism Theorem is separate.

## Implemented proof

The two generic lemmas in `RingRootCell.CellData` work over a commutative
ring, using the actual open cell of the supplied data. Put
`n = weylPoint D.xp D.xm` and let `n_d` rescale only the negative root by
`d`. Assume that conjugation by `n` takes `D.B(x)` to `D.A(-x)`.
The lemma `scalarWeylPoint_mul_weylPoint_inv` computes, on the base test,

```
n_d * n⁻¹ = D.cellPt (1-c) 1 (c-1),   c = baseScalar (base R) d.
```

It factors `n_d` as `D.B(1-c) * (n * D.B(1-c))`, then uses the
conjugation law. Constant-point restriction puts every factor on the same
test object.

If `n_d` and `n` have the same prescribed torus action, their quotient
centralizes the torus. Under the additional generic hypothesis
`torusCentralizer D.i = SubgroupFunctor.range D.i`, that quotient is a
torus point, hence has cell coordinates `0`, a torus point, and `0`.
Cell-coordinate injectivity gives `c = 1`. The global-sections isomorphism
of `Spec R` gives `d = 1`. This is
`scalar_eq_one_of_same_weyl_action`.

For the actual isolated rank-one centralizer, the lifted negative root
parametrizations differ by a unit by scalar rigidity, using pairing two
with the negative coroot. The lifted Weyl products retain their prescribed
reflection. Reductivity and fibrewise maximality of its torus supply
self-centralization, while `rankOneLaws_rootLift` supplies the required
root conjugation. The generic result forces the comparison unit to be one.
Composition with the centralizer inclusion recovers equality in `G`.
Finally, finiteness and reducedness of the fibrewise root datum supply
an isolating cocharacter for every root.
