# Cohomology of the cubic diagonal bundle over an algebraically closed field

`CubicFibreCohomologyStatement` is the geometric-fibre input to the
canonical direct-image theorem `CubicDirectImageStatement`. It concerns
the existing ordinary polarized datum `a : Datum P (Spec K) g d n` over an
algebraically closed field `K`, with `0 < d`. Put
`L = a.canonicalBundle`, the published diagonal Poincaré bundle attached to
the datum's polarization `lambda`, and `L^3 = a.cubicBundle`, its published
tensor cube. Write `pi = a.abelian.X.hom` for the structure morphism of the
abelian variety `A = a.abelian.X.left` to `Spec K`.

The statement asserts two things for every published `Prerequisites`, every
dimension `g`, positive index `d` and arbitrary level `n`:

1. for every `i > 0`, the cohomology `H^i(A, L^3)` is zero. Here
   `relativeCohomology pi i` is the published right-derived functor of the
   `K`-module global sections `relativeGlobalSections pi` on all
   `O_A`-modules;
2. the degree-zero cohomology `H^0(A, L^3)` has `K`-dimension `6^g*d`,
   expressed with Mathlib's `Module.finrank K`.

The level structure plays no role, so no condition on `n` is imposed.
No finiteness hypothesis is added: the finite-rank claim is part of the
assertion.

## Provenance

This is an internal statement, derived from the following sources. It
specializes them to the actual published datum and its canonical cubic bundle.

- Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, third edition
  (1994), registered as
  `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.
  Proposition 6.13 (i) and (iii) is on printed pages 123–124 / one-based PDF
  pages 136–137. For a relatively ample invertible sheaf on a projective
  abelian scheme it gives vanishing of the higher direct images. On an
  abelian variety this means `H^i(A, L) = 0` for `i > 0`. It also says that
  the degree of `Lambda(L)` is the square of the rank of the direct image.
  The footnote to Definition 7.5, printed page 130 / PDF page 143, applies
  this to the cube of the diagonal bundle of a polarization `omega` of
  degree `d^2`. By Proposition 6.10 the cube has `Lambda = 6 omega`, which
  has degree `6^(2g) d^2`. The footnote concludes that the rank is `6^g*d`.
- J. S. Milne, *Abelian Varieties*, author revision of January 2, 2022,
  registered as `milne-abelian-varieties-1986-author-2022`. Theorem 13.3 (a)
  and (c) is on page 25 (printed and PDF pages agree). It says that the
  degree of `phi_L` is `chi(L)^2`, and that if `K(L)` is finite exactly one
  cohomology group of `L` is nonzero. The proof of Theorem 14.1, page 26,
  uses these to show that `dim H^0(A, L^3) = chi(L^3)` for an ample `L`.

The intended argument over `K` runs as follows. The datum's polarization
is an isogeny of degree `d^2` that is the Mumford map of an ample bundle
over `K` (`Datum.polarized`, `Datum.degree`). The published diagonal
identity `PolarizationDiagonalMumfordStatement` (GIT Proposition 6.10,
proved in `PolarizationDiagonalMumfordProof`) gives `phi_L = 2 lambda`.
Then `L` is ample, as it is algebraically equivalent to the square of that
ample bundle. So `L^3` is ample with `phi_{L^3} = 6 lambda`. Vanishing
gives `dim H^0(A, L^3) = chi(L^3) >= 0`. Since `chi(L^3)^2` equals the
degree `6^(2g) d^2` of `6 lambda`, this dimension is `6^g*d`.

This module states the assertion and does not prove it. It establishes
neither ampleness, Riemann–Roch, nor any vanishing theorem.
