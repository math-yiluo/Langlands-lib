# The scalar of the weighted c-family on a common regular region

The inputs include the ambient and lower density packages with nonzero
canonical scalars and the common compact normalization
`CommonCompactNormalization`. The latter supplies the lower compact
inclusion for induction in stages. The proof uses a
`CompactContinuationSystem` on the common Levi with the Iwasawa
decompositions at its vertices, a nontrivial irreducible admissible
inducing representation, and a split component of the represented
parameter Levi. At each of `x` and `y` a supplied nonzero regular
function gives irreducibility of the corresponding induction on its
nonvanishing locus.

`exists_weightedCScalar_roundTrip` constructs regular functions `a` and
`d ≠ 0` on the translated parameter scheme, an open set `S` dense in the
unramified characters and on their unitary subgroup, and a constant `κ`. At
every point of `S`:

- all ordered pairs of the five vertices `θ`, `θ.opposite`, `x`,
  `x.opposite`, `y` are regular;
- `d` does not vanish and the inductions at `x` and `y` are irreducible;
- the outer round trip `J(x, y) J(y, x)` is a scalar `j` with
  `(a/d) · j = κ`.

Moreover, at every point of the weighted domain whose lifted parameter lies
in `S`, the actual density ratio `µ^G · (µ^{M'})⁻¹` equals `a/d`.

The proof combines `exists_weightedC_ambientRoundTrip`,
`exists_weightedC_lowerRoundTrip` and `exists_gallery_roundTrip_product`.
`weightedC_commonRegion` builds the region from the denominators of the
system and one nonzero product of regular functions. `weightedC_eight_ne_zero`
splits that product, and `weightedC_ratio_value` evaluates the fraction.
`weightedC_roundTrip_point` applies `gallery_roundTrip_point_product` and
`weight_mul_roundTrip_of_scalar_product` at each point. The constant is
`κ = (dG/dM) · s·t₀/t₁`. Here `dG` and `dM` are the density constants, `s` is
the gallery factor, and `t₀`, `t₁` are the positive Haar factors of the two
package comparisons.

This is the scalar identity in the proof of Lemma V.2.2 of Waldspurger,
printed pp. 293–294, where `xy = ∏ j_α(sω)` is computed by IV.3(2) and (4) and
cancelled against `µ^G(ω) µ^{M'}(sω)⁻¹`. The Lean statement keeps the positive
Haar factors in `κ` and needs only that the product is constant (source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).
