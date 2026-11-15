# The modulus of right multiplication on `𝔸^n`

Module `Langlands.Global.RankinSelberg.EqualAnalyticModulus`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

Main results:

- `rowModulus_eq_absDet`: for `g ∈ GL_n(𝔸)` the Haar character of `x ↦ x g` on `𝔸^n` is the
  idelic norm `|det g|` (`absDet F n g`).
- `map_rightMul_rectangleMeasure`: the image of `rectangleMeasure F 1 n` under `x ↦ x g` is
  `|det g|⁻¹ •` the measure.
- `integral_comp_rightMul`: `∫ f(x g) dx = |det g|⁻¹ ∫ f(x) dx`.
- `integrable_comp_rightMul_iff`.

## Provenance

The statement is classical: the modulus of a linear automorphism of `𝔸^n` is the norm of its
determinant (Weil, *Basic Number Theory*, Chapter I §2 locally, with the restricted product).
The proof here is internal and avoids local computations at the finite places. The Haar character
`rowModulus F n g` (Mathlib `addEquivAddHaarChar`) is multiplicative (`rowModulus_mul`).
`ρ = rowModulus / absDet` is therefore a homomorphism `GL_n(𝔸) → ℝ_{>0}`, and:

- `ρ = 1` on `GL_n(F)` (`rowModulus_rational`). `x ↦ x γ` carries the fundamental domain of `F^n`
  to another fundamental domain (`isAddFundamentalDomain_preimage_rightMul`), so it preserves the
  covolume one. Moreover `|det γ| = 1` (`absDet_rational`).
- `ρ = 1` on the archimedean torus `A(x) = diag(e^{x_i})` (`rowModulus_torInf`). In the product
  coordinates, `x ↦ x A(x)` is the coordinatewise real scaling `scaleRow` on `(F_∞)^n` times the
  identity (`rowSplit_rightMul_torInf`). Its determinant is `Π_j e^{d x_j}` (`det_scaleRow`, with
  Mathlib `LinearMap.det_pi`, `det_smul` and `Measure.map_linearMap_addHaar_eq_smul_addHaar`).
  That is the Library's `absDet_ofInfinite_torInf`.
- `ρ` is bounded on compact sets (`exists_rowModulus_le`): `|K₀ q| ≤ |K₀ Q|` for a compact
  neighbourhood `K₀` of `0`.

By the Library's Siegel decomposition `γ g = A(x) q` with `q` in a fixed compact set
(`exists_siegelDecomposition`), `ρ` is bounded on `GL_n(𝔸)`. A bounded homomorphism to `ℝ_{>0}`
is trivial, because the powers of a value other than `1` are unbounded.

## Other declarations

`rightMul F n g` (the continuous additive automorphism `x ↦ x g`), `rightMul_apply`, `rightMul_mul`,
`rowModulus_pos`, `rowModulus_one`, `rowModulus_inv`, `rightMul_rational_ratRow`, `scaleRow_apply`,
`splitHaar` (the Haar measure transported from the product), `map_rightMul_torInf_splitHaar`,
`absDet_one`.
