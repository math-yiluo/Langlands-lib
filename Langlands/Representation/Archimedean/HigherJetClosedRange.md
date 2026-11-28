# Closed range of a higher jet with a scaled inverse

`HigherJetClosedRangeStatement` concerns two complex vector spaces `E` and
`F` with topologies and a Hausdorff topology on `E`. The `m` coefficient
coordinates of a jet carry the product topology. The operator `shift m k`
is multiplication by the parameter to power `k` modulo parameter degree
`m`. Assume `2k ≤ m` and that continuous complex-linear maps `T` and `S`
between the two `m`-jet spaces compose in both orders to `shift m k` on
the respective space. Then the range of `T` is closed.

## Proof

The range of the `k`-shift consists of the jets with the coefficients of
indices less than `k` equal to zero. Lean constructs a preimage by moving
the remaining coefficients backwards, padding with zeros. The range is
closed by continuity of the coordinate projections and Hausdorffness. If
`2k ≤ m`, every coefficient of index less than `k` appears in the shifted
jet, so the kernel of the shift lies in its range.

The abstract preimage identity in `range_eq_preimage` uses both scaled
inverse identities. If `S y = (shift m k) x`, then `y − T x` is killed by
`S`, hence by the shift on `F`-jets. It thus lies in the shift range, which
lies in the range of `T`. This shows that the range of `T` is the preimage
under `S` of the shift range on `E`-jets. Continuity of `S` gives closedness.

The split-projection lemma `isClosed_range_comp_iff_of_rightInverse` is
also useful for the specialization to the constant coefficient. The
preimage of the projected range is the sum of the original range and the
projection kernel. Passing back through a continuous right inverse of the
projection proves the converse closedness implication. Casselman's
constituent induction supplies the additional sum-closedness step for
Langlands quotients in Theorem 10.4.

## Source

This is the coefficient-space calculation of W. Casselman, *Canonical
extensions of Harish-Chandra modules to representations of G*, Canadian
Journal of Mathematics 41 (1989), Proposition 9.3, printed p. 430 (PDF p. 46).
In one parameter, the invertible factor of the scalar in the two inverse
identities can be absorbed into the inverse map, giving the pure shift
by the vanishing order used here. The formal hypothesis supplies the two
continuous maps on the jet spaces. The specialization discussion uses
Theorem 10.4, printed pp. 431–432 (PDF pp. 47–48).
Registered source `casselman-1989-canonical-extensions`, SHA-256
`3617eaddaecf238b98152ce8eb7f52811a931b5a9dda6b33a1012c026f802f5a`.
[Casselman, §§9–10](https://doi.org/10.4153/CJM-1989-019-5)
