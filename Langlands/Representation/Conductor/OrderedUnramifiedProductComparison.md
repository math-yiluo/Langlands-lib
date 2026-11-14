# Unramified principal series as a normalized product of rank-one blocks

Module `Langlands.Representation.Conductor.OrderedUnramifiedProductComparison`.

## Purpose

`Conductor.UnramifiedPrincipalSeries` defines the unramified principal series
`principalSeries hϖ n hq z` of `GL_{n+1}(F)`. It is the smooth induction, from the upper
Borel, of the normalized character `δ_B^{1/2} · ∏ χ_{z_i}`. Here
`χ_{z_i}(a) = z_i ^ ord(a)` and `δ_B^{1/2}` is the explicit half modulus
`halfModulusCharacter`. The all-field port of the Bernstein–Zelevinsky derivative
results (namespace `Langlands.AllFieldBZ`) states its results for the normalized product
induction `T.normalizedProductInductionFunctor B` of block representations. This module
identifies the first construction with the second for the singleton block shape. The
derivative results can then be applied to the principal series. This is internal glue:
the identification is the standard description of a principal series as
`χ_1 × ⋯ × χ_{n+1}`. Bernstein–Zelevinsky (*Induced representations of reductive
p-adic groups I*, 1977) define this product of `GL_1` characters by normalized
parabolic induction from the Borel. The module adds no new mathematics beyond that
description.

## Contents

- `pkg F`, `data F`: the all-field package `LocalFieldPackage.ofField F` and the
  local-field data built from the given instances of `F`.
- Arithmetic: `data_ord` (the package valuation `ord` equals `ord hϖ` of
  `UnramifiedPrincipalSeries`), `data_residueCardinality`, and `data_normalizedAbs`
  (`|a| = q ^ (-ord a)`). The uniformizer has package order one
  (`data_ord_uniformizer`), because its order times any element's order is one and
  its valuation is below one.
- `pairSum_eq`: the identity
  `∑_{i<j} (o_j - o_i) = -∑_i (n - 2i) o_i` of integer exponents.
- `toParabolic`: the Borel, identified with the parabolic of the singleton block shape
  through `borel_eq_singleton_parabolic`. The underlying matrices are unchanged
  (`toParabolic_val`).
  `determinant_leviProjection_toParabolic`: the determinant of the `i`-th
  singleton Levi block is the `i`-th diagonal entry.
- `leviModulus_toParabolic`, `leviHalfModulus_toParabolic`: the all-field Levi modulus
  `∏_{i<j} |b_ii| / |b_jj|` of a Borel element is `q ^ (-∑_i (n-2i) ord b_ii)`. Its
  positive square root, cast to `ℂ`, equals `halfModulusCharacter hϖ n hq b`.
- `external_eq_smul`: if each factor group acts on its factor by a scalar
  `c_i(g)`, the external tensor product action is multiplication by `∏ c_i(m_i)`.
- `blockInducing n X`: the inducing representation of the parabolic in the normalized
  product induction of the blocks `X`. It is stated over the package carrier
  `(pkg F).Carrier` with the package topology, as in the port's functor.
- `normalizedCharacter_eq_levi`: the normalized Borel character equals the Levi half
  modulus times the product of the block characters `χ_{z_i}(det m_i)`.
- `characterEquiv`: given a linear identification `E` of the block tensor product with
  `ℂ`, whose blocks act by `g ↦ χ_{z_i}(det g)`, `E.symm` is an equivalence
  between the normalized Borel character representation and `blockInducing n X`
  pulled back along `toParabolic`.
- `principalSeriesEquiv`: under the same hypotheses, the principal series is
  equivalent to the representation of
  `((data F).normalizedProductInductionFunctor (blocks n)).obj X`. The proof is
  `characterEquiv` induced to `GL_{n+1}(F)` (`Induction.smoothInducedEquiv`), followed by a
  local transport of smooth induction along the equality of the Borel with the singleton
  parabolic (`smoothInducedSubgroupCongr`, proved by `subst`). The last step is
  definitional: the functor's object is the smooth induction of `blockInducing n X`.
- `lineEquiv`: a finite tensor product of lines `V_i ≃ ℂ` is identified with `ℂ`
  (`PiTensorProduct.congr` followed by `PiTensorProduct.constantBaseRingEquiv`).
  This builds the `E` argument from one-dimensional blocks.

## Lean notes

`LocalFieldPackage.ofField` is a plain definition, so instance search does not
identify `(pkg F).Carrier` with `F`. Statements that face the port are therefore
written over `(pkg F).Carrier`, with `letI := (data F).topology` and
`isTopologicalRing_data`. Rewriting with port lemmas uses `erw`, or `congrArg` and
`trans` terms.
