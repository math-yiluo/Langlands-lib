# The radical of the standard Iwahori order and its cyclic coordinates

Lean module: `Langlands.Representation.AffineGeneric.Radical`, namespace
`Langlands.AffineGeneric`.

Let `F` be a field with a valuative relation, valuation ring `𝒪 = integers F`, maximal ideal `𝔭`
and residue field `k = Residue F` (`IsLocalRing.ResidueField (integers F)`).

## Residues

- `resOf x` is the residue class of `x` when `x` is integral and `0` otherwise. The lemmas
  `resOf_add`, `resOf_mul` (for integral arguments), `resOf_eq_zero_iff`, `resOf_of_lt_one`,
  `resOf_add_of_lt_one`, `resOf_neg`, `resOf_sum`, `resOf_zero`, `resOf_one` describe it as a ring
  homomorphism on `𝒪` killing `𝔭`.
- `exists_resOf_eq`: every residue is `resOf x` for an integral `x`.
- `val_eq_one_of_resOf_ne_zero`: an integral element with nonzero residue is a unit of `𝒪`.
- `resOf_eventuallyEq`: when `F` is a nonarchimedean local field, `resOf` is locally constant.

## The Iwahori order and its radical

Matrices are indexed by `Fin (m + 1)`.

- `IsIwahoriOrder M`: every entry of `M` is integral and the entries strictly below the diagonal
  lie in `𝔭`. This is the standard Iwahori order `𝔄`.
- `IsIwahoriRadical M`: every entry is integral and the entries on and below the diagonal lie in
  `𝔭`. This is the Jacobson radical `𝔓` of `𝔄`.
- `isIwahoriOrder_one`, `isIwahoriRadical_zero`, `IsIwahoriRadical.add`, `.neg`, `.smul`
  (integral scalars), `IsIwahoriOrder.mul`, `IsIwahoriOrder.mul_radical`,
  `IsIwahoriRadical.mul_order`: `𝔄` is closed under products and `𝔓` is a two-sided `𝔄`-ideal.
- `IsIwahoriOrder.resOf_mul_diag`: on `𝔄`, the residues of the diagonal entries are
  multiplicative, `res((MN)ᵢᵢ) = res(Mᵢᵢ) res(Nᵢᵢ)`.

## Cyclic coordinates

Fix `ϖ ∈ Fˣ` and write `ρ = finRotate (m + 1)`, so `ρ i = i + 1` for `i ≠ last` and
`ρ last = 0`.

- `weight ϖ i` is `ϖ⁻¹` for `i = last` and `1` otherwise.
- `coord ϖ Y i = resOf (weight ϖ i * Y i (ρ i))` defines `aᵢ(Y)`. The argument of `resOf`
  is the superdiagonal entry `Y i (i + 1)` for `i ≠ last` and `ϖ⁻¹ Y last 0` for `i = last`.
  For `m = 0` the formula is `resOf (ϖ⁻¹ Y 0 0)`. For all `m`, `resOf` returns `0` whenever
  the weighted entry is nonintegral.

For a uniformizer `ϖ` (`Iwasawa.IsUniformizingElement`) and `Y ∈ 𝔓`:

- `val_weight_mul_le_one`: the weighted entry defining each coordinate is integral;
- `coord_add`, `coord_smul`: the coordinates are additive and `𝒪`-linear on `𝔓`;
- `coord_order_mul`, `coord_mul_order`: for `M, N ∈ 𝔄`,
  `aᵢ(M Y) = res(Mᵢᵢ) aᵢ(Y)` and `aᵢ(Y N) = aᵢ(Y) res(N_{ρ i, ρ i})`;
- `coord_mul_radical`: the coordinates vanish on products `Y Z` with `Y, Z ∈ 𝔓`.

Each proof expands the relevant matrix entry as a sum and checks that all terms except the
displayed one lie in `𝔭`, using that `i < ρ i` for `i ≠ last` (`lt_finRotate_of_ne_last`) and
the valuation bounds `val_le_uniformizer`, `val_inv_mul_le_one`, `val_inv_mul_mul_lt_one`.

## Origin

`I⁺ = 1 + 𝔓` is the pro-unipotent radical of the standard Iwahori subgroup. Assume `ϖ` is a
uniformizer for the coordinate interpretations below.

**Case `m ≥ 1`.** The coordinates on `𝔓` correspond to the `m + 1` affine simple roots of
`GL_{m+1}`. They sit at the entry positions `(i, i + 1)` for `i < m` and `(m, 0)`, the latter
scaled by `ϖ⁻¹`. Knightly–Li use this matrix formula on `I⁺` with nonzero coefficients and a
nontrivial additive character of `k` in Section 2, p. 997, (2.1)–(2.2). Gross–Reeder define
affine generic characters through the simple affine root quotients for split simply
connected almost simple groups in Section 9.2, manuscript pp. 60–62. The type `A` instance
there is `SL_n`. [Knightly–Li](https://doi.org/10.11650/tjm.19.2015.3853),
[Gross–Reeder](https://people.math.harvard.edu/~gross/preprints/AdjointGamma5.pdf).

**Case `m = 0`.** The root system of `GL_1` is empty. Here `I⁺ = 1 + 𝔭` and `ρ` fixes the
only index `0`. The formula gives the principal-unit homomorphism
`g ↦ a₀(g - 1) = res(ϖ⁻¹ (g - 1))` to the additive group of `k`. The equality
`ϖ𝔭 = 𝔭²` gives its kernel `1 + 𝔭²`.

The definitions here are elementary matrix conditions; the lemmas are direct computations.
