# The enveloping algebra of an abelian Lie algebra as a polynomial ring

Module `Langlands.Algebra.AbelianEnvelopingPolynomial`, namespace
`Langlands.Algebra.AbelianEnveloping`.

Let `M` be a Lie algebra over a field `k` with `⁅x, y⁆ = 0` for all `x, y` (hypothesis `hab`).

- `ι_commute`, `mem_center`: the generators commute, so every element of `U(M)` is central. The
  centre is a subalgebra containing the generators, which generate `U(M)`
  (`LieCasimir.enveloping_adjoin_range`).
- For a finite basis `c : Basis J k M` and a complete duplicate-free list `l` of indices,
  `toPoly hab c : MvPolynomial J k →ₐ[k] Subalgebra.center k U(M)` sends `X a` to `ι (c a)`.
  `toPoly_monomial`: it sends `X^α` to the ordered monomial with exponent `α` (the product is
  computed in the commutative centre).
- `pbwPoly_toPoly`, `toPoly_pbwPoly`, `toPoly_bijective`: `toPoly` and the PBW coordinate map
  `LieEnvelopingSymbol.pbwPoly` are mutually inverse, so `toPoly` is bijective.
- `polyEquiv`: the resulting algebra isomorphism. `polyEquiv_symm_apply`,
  `coeff_polyEquiv_symm`: the inverse sends a central element to the polynomial of its ordered
  PBW coordinates.

## Provenance

The Poincaré–Birkhoff–Witt theorem for an abelian Lie algebra: its enveloping algebra is the
symmetric algebra, a polynomial ring on a basis. The proof uses the Library's ordered PBW basis.
