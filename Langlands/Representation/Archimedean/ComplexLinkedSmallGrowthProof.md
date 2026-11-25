# Small growth in the dual of a linked standard module, from unlinked swaps

## Statement

```lean
def ComplexLinkedSmallGrowthReductionStatement : Prop :=
  ComplexStandardUnlinkedSwapStatement → ComplexLinkedSmallGrowthStatement
```

`ComplexStandardUnlinkedSwapStatement` (Library, module `ComplexStandardUnlinkedSwap`) provides,
for all lists `pre`, `post` and unlinked complex characters `d`, `e` with
`(pre ++ d :: e :: post).length = n`, a bijective `(𝔤, K)`-intertwining map from the
`U(n)`-finite functions of the standard module of `pre ++ e :: d :: post` to those of
`pre ++ d :: e :: post`. `ComplexLinkedSmallGrowthStatement` (Library, module
`ComplexLinkedLanglandsQuotientGrowth`) asks, for a Langlands-ordered list `ds` of `n` complex
characters two of which are linked and a list `ds'` of pointwise inverse position characters,
for a nonzero finite-dimensional `U(n)`-stable subspace `E` of the `U(n)`-finite functions of
the standard module of `ds'` with `dim U_d(𝔤) · E ≤ C (d + 1)^{n(n-1)-1}` for all `d`.

The theorem `complexLinkedSmallGrowthReduction` proves the statement.

## Provenance

Internal reduction statement, between two statements already in the Library. It
belongs to an independent internal proof of the complex case of the conclusion of Vogan's
theorem on large standard modules (D. Vogan, *Gelfand–Kirillov dimension for Harish-Chandra
modules*, Invent. Math. 48 (1978), Theorem 6.2, (a) ⇒ (f)). This dimension-count route is not
Vogan's argument: Vogan's proof on p. 93 reduces to nonsingular infinitesimal character by
translation and then derives a nonempty τ-invariant from reducibility (Speh–Vogan), which
contradicts largeness. Here the growth argument is the one described below. With the proof
`complexStandardUnlinkedSwapReduction complexGLTwoUnlinkedIrreducible` of
`ComplexStandardUnlinkedSwapStatement`, the reduction gives
`ComplexLinkedSmallGrowthStatement`, which with `ComplexStandardHolomorphicGrowthStatement`
yields `ComplexLinkedLanglandsQuotientNotLargeStatement`
(`complexDualSubmoduleAnnihilator_of_growth`, `complexLinkedLanglandsQuotientNotLarge_of_dualSubmodule`;
assembled in `ComplexLinkedLanglandsQuotientNotLargeProof`).

## Proof (`LinkedSmallGrowth.complexLinkedSmallGrowth_of_unlinkedSwap`)

1. The position characters of `ds'` are those of `ds.map complexCharacterDataInv`
   (`complexPositionCharacter_map_inv_mul`), so the goal is
   `SmallGrowth n (complexPositionCharacter (ds.map complexCharacterDataInv))`
   (`SmallGrowthTools.SmallGrowth`).
2. `exists_minimal_linked`: write `ds = pre ++ d :: (mid ++ e :: post)` with `d`, `e` linked and
   `mid` of minimal length; then no character of `mid` is linked with `e`
   (`exists_linked_decomp` gives some decomposition). The Langlands order gives
   `Re e.exponent ≤ Re d.exponent`, so the linkage integers `p = x_d - x_e`, `q = y_d - y_e`
   (`p q > 0`) satisfy `p + q = 2 Re(d.exponent - e.exponent) ≥ 0`, hence `p, q > 0`.
3. In the inverse list, `L0 = P ++ d⁻¹ :: e⁻¹ :: (mid⁻¹ ++ post⁻¹)` with `P = pre⁻¹` has, at the
   positions `|P|`, `|P| + 1`, weights `-d.weight`, `-e.weight` and exponents `-d.exponent`,
   `-e.exponent` (`posWeight`, `posExponent`, `complexPositionCharacter_eq_phase`,
   `posWeight_append`, `posExponent_append`). Thus `l_{i+1} - l_i = p - q` and
   `t_{i+1} - t_i = (p + q)/2`, and `AdjacentGrowth.smallGrowth_adjacent` gives `SmallGrowth` for
   `L0`.
4. `smallGrowth_move`: moving `e⁻¹` to the right past the characters `m⁻¹` of `mid⁻¹`, none linked
   with it (`not_linked_inv`: linkage is invariant under inversion), carries `SmallGrowth` from
   `L0` to `ds.map complexCharacterDataInv`. Each step (`smallGrowth_swap`) uses the bijective
   intertwining map of `ComplexStandardUnlinkedSwapStatement` with
   `IsComplexStandardIntertwining.map_complexStandardRep`, `map_complexStandardLie` and
   `SmallGrowthTools.smallGrowth_of_intertwine`.

## Supporting modules

The adjacent case is assembled in `ComplexLinkedSmallGrowthAdjacent` from:
`RealPolynomialFunctions`, `RealPolynomialMatrices`, `FiniteFunctionSpaces`,
`ComplexLevelFunctions`, `ComplexLevelPrincipalSeries`, `ComplexLevelSpan` (the space `E`),
`ComplexBlockPolynomial`, `ComplexLevelBlockPolynomial` (polynomiality along the root subgroup),
`ComplexNoncompactPicture`, `ComplexTorusDerivative`, `WeightedPolynomialDerivative`,
`ComplexNoncompactFiltration` (the filtration raised by right derivatives),
`ComplexNoncompactDimension` (its dimension bound), `ComplexSmallGrowthTools`, and the Library
module `ComplexLowerUnipotentRestriction`.
