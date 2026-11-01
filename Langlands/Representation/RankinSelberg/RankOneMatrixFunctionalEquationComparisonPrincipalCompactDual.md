# Principal compact dual extraction with the actual complementary block

This internal derived module composes compact signed Fourier pairing, the
uniform principal-box extraction, and full compact-parameter convergence. It
retains the actual signed Weyl representatives and the same supplied additive
character and self-dual Haar measure. The result concerns compact functions
in scalar standard-character induction, not yet arbitrary coefficient-model
vectors or a gamma functional equation.

For `m ≥ 0`, put `n = m + 1` and `r = m + 2`. Let `f` be an actual compact
standard-Whittaker induced function on `GL_r`. Compactness means compact
projected support modulo the upper-unipotent subgroup. Write `W` for the signed
long Weyl representative and `B` for the signed complementary block Weyl
representative. The definition `principalSignedBlockPoint F m k (g,Z)` is the
literal group product

```text
H(k,g,Z) = blockMatrixAt m 0 g Z · B · inverseTranspose(k).
```

The rectangular block has size `m × 1`; no block variable is discarded. The
definition `principalCompactDualIntegrand` evaluates `f` at this group point.
It does not identify the point with any unsigned or dual-model function.

Let `q` be the conductor of the arbitrary supplied nontrivial unitary additive
character `ψ`, let `a > 0`, and assume `q + a ≥ 0`. Set

```text
Psi = boxLatticeTest F (q+a) q a,
C = boxExtractionConstant F (n := m+1) (q+a) q a,
mu = principalAveragingMeasure F (n := m+1) a C.
```

The existing box result makes `C` strictly positive. The same `mu`, supported
on the actual principal subgroup at level `a`, has total mass `C`. Its elements
have determinant norm one almost everywhere. The scalar measure below is the
existing `glOneMeasure F (m+1)`, whose density relative to the actual `GL_1`
Haar measure is `|det g|^(-(m+1))`. The block measure is the actual
`rectangularMeasure nu m 1` of the supplied self-dual additive measure `nu`.

The theorem `principalCompactDual_pairing` proves both genuine integrabilities
and the equality

```text
integral_h f(h) Fourier(Psi)(W h) dh
  = integral_(k,g,Z) f(H(k,g,Z)) d(mu × glOneMeasure × blockMeasure).
```

The right measure is bracketed as `mu × (glOneMeasure × blockMeasure)`, as in
Lean. The Fourier transform is the plus entry-product pairing for the same
`ψ` and `nu`. There is no further scalar, Jacobian, conductor restriction, or
normalization of the supplied measure.

The implemented proof first makes `principalCompactKernel`, the compact open
principal-subgroup indicator. It is one `mu`-almost everywhere and its support
has determinant norm one. The full product theorem of CompactGLParameters
applied to this indicator and the identity translate proves convergence of
both natural-weight orbit kernels while retaining `k` outside the orbit
integral. Thus cancellation within the compact average is never used to infer
absolute convergence.

The helper `glOneWeight_eq_determinantWeight` identifies the real scalar
density with the corresponding complex determinant power. Its consequence
`glOneWeight_smul_natSucc` states that the density times the ambient natural
exponent `r` leaves scalar exponent one. The literal complementary block has
the determinant of `g`. The signed block Weyl has determinant norm one, as
does the inverse transpose of a parameter of norm one. This proves
`determinantWeight_principalSignedBlockPoint`. Pointwise weighted lift
reconstruction then identifies the block kernel with the density times the
actual input `f(H(k,g,Z))`. On the Fourier side the actual natural-weight
signed Fourier orbit gives the parallel pointwise identity.

The two parameter-density lemmas retain the other factors of the product
measure when passing to `glOneMeasure`. Applying the Bochner with-density
integrability equivalence transfers the established full product bounds to
the displayed restrictions. The theorem
`principalCompactDual_fourierOrbit_duality` gives the resulting full-product
identity for any real parameter `C` in the principal averaging measure. Only
after those bounds are established does Fubini identify the Fourier side
with the scalar integral of the principal average. The theorem
`principalMeasure_extraction` applied to the smooth standard-equivariant
signed Fourier orbit and `compact_signedFourier_pairing` with the actual box
then give the displayed compact pairing.

Finally, `principalCompactDual_pairing_weighted` proves, for every `s : ℂ`,
genuine integrability and the equality

```text
integral_h (|det h|^s f(h)) Fourier(Psi)(W h) dh
  = integral_(k,g,Z) |det g|^s f(H(k,g,Z))
      d(mu × glOneMeasure × blockMeasure).
```

The implemented twist is
`weightedCompactFunction ... (-s) f`, which evaluates to `|det h|^s f(h)`.
It is an actual compact group function. On the block side the proved
norm-one parameter identity replaces the determinant weight of `H(k,g,Z)`
by that of `g` almost everywhere. The box test, principal measure, block
measure and averaging parameter are unchanged for every exponent. No complex
determinant twist of a test on the singular full-matrix locus is asserted to
be Schwartz–Bruhat.

The provenance is source-free composition of the cited internal synthesis,
signed orbit, compact-family, principal extraction and Haar-density APIs.
The canonical field may lie in any universe and `m = 0` is included (with an
empty complementary rectangle). Extending these identities to arbitrary
coefficient-model vectors still requires the actual weighted restrictions
to be integrable. This module neither assumes nor establishes the host gamma
comparison, its analytic continuation, unsigned sign conversion, or quotient
measure and functional transport.
