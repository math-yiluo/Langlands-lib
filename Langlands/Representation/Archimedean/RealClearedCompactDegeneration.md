# Finite polynomial specialization to binomial and canonical tail operators

This derived internal unit specializes the explicit cleared finite spectral
families of `RealRationalCompactFamilies`. At positive resonance they equal a
nonzero scalar times the binomial spectral operator. At a negative pole they
equal a nonzero scalar times the canonical tail spectral operator, provided
the denominator bound exceeds the pole index. These are finite evaluation
identities; no operator limit is used.

Let `eps` be zero or one and
`ell = eps.toNat + 2r + 1`. Put
`pole(eps,r) = -(eps + 2r + 1)`. The denominator in a bound `B` is the product
of `eps + 2i + 1 + nu` for `i < B`. Its value with the factor at `r` removed
is `poleComplement eps B r`. Every remaining factor is nonzero at the pole,
so the complementary product is nonzero.

For `r < B` and a sequence index `m ≤ B`, `clearedSeq_at_pole` proves

`clearedSeq(eps,B,m;pole) =
 poleComplement(eps,B,r) * regularizedSeq(pole,eps,r,m)`.

If `m ≤ r`, the unused denominator product in the cleared numerator contains
the vanishing factor at `r`, and both sides are zero. If `r < m`, split the
erased denominator product into indices below `m` and indices from `m` to `B`.
The explicit regularized product cancels its nonzero denominator product below
`m`. This gives the identity directly by finite-product algebra.

The reflection factors in `clearedMultiplier` and `regularizedMultiplier`
are the same. Extending the sequence identity therefore covers every integer
mode. The proved scalar degeneration of Worker 769 then identifies the
regularized multiplier with its nonzero first-high-index value times the
canonical tail. The displayed scalar is

`tailScale(eps,B,r) =
 poleComplement(eps,B,r) * regularizedSeq(pole,eps,r,r+1)`.

It is nonzero. The tail symmetry is precisely
`(-1)^eps.natAbs`; no differential-sign substitution is made.

At a positive resonant parameter `ell`, the common denominator is nonzero.
The existing clearing formula and the proved binomial degeneration give

`clearedMultiplier(eps,B;ell,j) =
 positiveScale(ell,B,eps) * binomialMultiplier(ell,eps,j)`

for every index with `abs(j)/2 ≤ B`, where

`positiveScale(ell,B,eps) =
 product(i < B) (eps+2i+1+ell) / binomialSeq(ell,eps,0)`.

The numerator factors and the binomial base are nonzero, so this scalar is
nonzero as well.

`clearedSpectral_tail` and `clearedSpectral_binomial` sum these exact scalar
identities against any fixed finite family of projections. In compact degree
`N`, the integer modes lie in `[-N,N]`, so their half absolute indices are at
most `N`. The corollaries `compact_tail` and `compact_binomial` apply to the
actual finite compact polynomial model with bound `B=N`. The tail corollary
retains `r < N`, ensuring the removed pole factor belongs to the chosen common
denominator.

`RealClearedCompactDegenerationStatement` packages the two nonzero-scalar
compact operator formulas, for every scalar polynomial parameter `q` and
parameter pair `z` having the specified evaluation. The positive assertion
assumes `ell>0` and `ell-1-eps` even; the negative assertion additionally
supplies the displayed half-index `r` and `r<N`.
`realClearedCompactDegeneration` proves the proposition.

The proof uses explicit generic and regularized products, the previously
proved scalar binomial/canonical-tail degenerations and finite spectral sums.
Worker 769 supplied those scalar degenerations. No full generic or canonical
braid, relation with the chosen interlaced equivalence, or filtration
kernel-image containment is asserted.
