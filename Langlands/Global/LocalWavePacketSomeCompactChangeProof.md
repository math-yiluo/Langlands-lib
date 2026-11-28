# Changing the compact subgroup in Lapid’s wave-packet formula

`Langlands.Global.localWavePacketSomeCompactChange` proves
`Langlands.Global.LocalWavePacketSomeCompactChangeStatement`. It applies
`LocalWavePacketSectionSomeCompactStatement` to the parabolic data of
`LocalWavePacketInnerProductStatement` and writes `L` for the maximal compact
subgroup it supplies. The input packets use an arbitrary maximal compact
subgroup `K` with Iwasawa decompositions for the two parabolics.

## Transport of the operators

Choose an infinite adelic point `s` with `s K∞ s⁻¹ = L∞`. For each parabolic
use the height difference
`Δ(g) = H_K(gs) − H_L(g)`. It is the height difference for `s K s⁻¹` and `L`
plus the constant `H_K(s)`. The compacts in that difference have the same
infinite projection. Its fibres depend only on the finite adelic coordinate
and are clopen, with finitely many values `u`. A fixed inducing form `v`
gives the inducing family with vectors
`v_u(g) = 1_{Δ(g)=u} v(gs)` and coefficients `exp⟨λ,u⟩`. Each vector lies in
`A²` for `L`. [AdelicWavePacketCompactCutoffs](AdelicWavePacketCompactCutoffs.md)

The `K`-twist at `gs` is the sum of the `L`-twists of `v_u` at `g` with these
coefficients. The proof uses absolute convergence for the cut Eisenstein
terms and integrability for the cut intertwining terms to pass the finite
sums through the series and integrals in the regular region. In the
intertwining comparison it first twists both operators at `wλ` to identify
their integrals. Expanding the old operator and cutting its target vectors
produces the same target twist as the new operator sum. The common nonzero
height factor for `L` then cancels. Each transported expansion coefficient
is the original coefficient times `exp⟨wλ,u'⟩` for the corresponding target
fibre `u'`.

The exponential coefficients are entire in linear coordinates. The
Eisenstein continuation for a transported family is `E_j(λ)(gs)` on the
supplied domain of `E_j`. Transport therefore uses the given local
regularity of the finite combination and keeps the packet coefficients and
spectral measures. This is the role of holomorphic families in the premise.

## The two pairings

The two packets for `L` are the right translates of the original packets.
Left rational invariance follows from scalar meromorphic uniqueness for
the supplied continuations and from the support conditions. Right
translation is measure preserving on the full rational quotient, which
transfers both `MemLp` conclusions and the quotient integral.

On the spectral side the proof compares the normalized inducing pairings
on the common discrete parabolic quotient. It uses Iwasawa-compatible Levi
measures for both compacts and shifts the height weight on each fibre. A
central Levi translation absorbs that shift. The pairings of distinct cut
pieces vanish. The Weyl parameter carries imaginary parameters to imaginary
parameters, so the exponential on a diagonal fibre times its conjugate is
one. Summing the diagonal cut pairings therefore gives the original
spectral integrand. [AdelicInducedPairingCompactChange](AdelicInducedPairingCompactChange.md)

## Provenance

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, Clay Math. Proc. 13 (2011), §2, pp. 311–312, for
  the choice of compact, compatible measures, inducing square norm and
  Eisenstein and intertwining operators. §3, p. 314, gives the wave-packet
  space and Proposition 2, formula (4). The termwise imaginary-axis
  holomorphy is Proposition 6, p. 329. Retained volume PDF
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, pages 320–321,
  323 and 338, SHA-256
  `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
  series*, J. Amer. Math. Soc. 37 (2024). Section 2.1, p. 190, specifies the
  compact and the corresponding height map. Section 2.2, p. 191, gives the
  inducing twist, the Eisenstein series in (2.1), and the twisted
  intertwining operator in the unnumbered display. Footnote 1 normalizes
  Haar measure on `V(𝔸)` so that `V(F) \ V(𝔸)` has volume one for each
  unipotent `F`-group `V`.
  Retained journal PDF `bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
  pages 4–5, SHA-256
  `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
