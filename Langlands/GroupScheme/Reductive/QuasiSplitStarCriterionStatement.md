# Splitting of a quasi-split group from its absolute star action

`Langlands.GroupScheme.QuasiSplitStarCriterionStatement` concerns a
quasi-split group \(G\) over an arbitrary field \(k\). Its structure
morphism is affine and locally of finite type. For every choice of
`GaloisPinningData` over \(k^s\), the group has a split maximal torus over
\(k\) if and only if every element of \(\operatorname{Gal}(k^s/k)\) acts
as the identity through `d.starAction`. This action is on the full
based root datum on the actual lattices of the torus after scalar
extension. In particular, the identity condition includes the action
on central character directions.

## Source and derivation

J. S. Milne, *Algebraic Groups* (2017), registered source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

Definition 19.22, printed p. 402 (PDF p. 418), identifies splittability
with the existence of a split maximal torus. The Weyl correction is
defined in §25.c, printed pp. 551–552 (PDF pp. 567–568), and §25.d,
printed p. 554 (PDF p. 570), uses its action on the character lattice.
Proposition 25.28(a) and Example 25.37, printed pp. 552 and 557
(PDF pp. 568 and 573), use a torus in a rational Borel for a quasi-split
group. For this choice the positive roots and base are Galois stable,
so the Weyl correction is the identity on the full root datum.
Theorem 12.23, printed p. 240 (PDF p. 256), then identifies a torus
with trivial absolute action on its character lattice with the split
torus of that lattice.
Conversely the ordinary lattice action on a split maximal torus is
trivial, so its Weyl-corrected action is also trivial. Transport
between based root data gives the criterion for every choice of pinning.
