# Frobenius maps between real standard modules along a block

Module: `Langlands.Representation.Archimedean.RealBlockFrobeniusMap`, namespace
`Langlands.Archimedean.RealBlockFrobeniusMap`.

## Purpose and provenance

Let `ds` and `es` be lists of real blocks of rank `n` (module `StandardModule`). Their
position characters agree off the positions `p, p + 1`, and the exponents are exchanged at
these positions. This module builds linear maps from the `O(n)`-finite functions of the real
standard module of `ds` to those of `es` by Frobenius reciprocity. It uses the construction
`frobFun` of module `RealJacquetFrobeniusProof` and the block Jacquet functionals
`ℓ_μ = blockJacquet n ds p μ` of module `RealBlockJacquetFunctional`,
`ℓ_μ(f) = (2π)⁻¹ Σᶠ_j μ_j Φ_j(f)(1)`, where `Φ_j = blockFourierCoefficient n p j` and
`μ : ℤ → ℂ` is a multiplier sequence (module `RealBlockMultiplier`).

For a multiplier `μ` that satisfies the recurrence `IsRecurrent δ ε μ` for
`δ = t_p - t_{p+1} + 1`, where `t` are the exponents of `ds`, the map is an intertwiner. On
`O(n)` it multiplies the `j`-th block Fourier coefficient by `μ_j`. This turns questions about
the image and kernel of intertwiners into questions about the zeros of `μ`.

This module is internal infrastructure for the proof of
`Langlands.Archimedean.RealCharacterPairFiltrationStatement` (Task 7067). Its contents are
derived here, so it has no literature sources. The structure `IsBlockFrobData` and the map
`blockFrobMap` are internal notation.

Notation: `K(ds) = kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`. The
signs, exponents and characters at the positions are `realPositionSign`,
`GramFormula.realPositionExponent` and `realPositionCharacter`, and `realInducedBlockAt` gives the
induction blocks (modules `StandardModule` and `RealBlockPositionData`).

## Declarations

### The data

`IsBlockFrobData n ds es p ε σ μ : Prop` is a structure with the following fields:

- `lt : p + 1 < n` and `rank : realRank es = n`;
- `sign_off`, `exp_off`: at every position `i ∉ {p, p + 1}`, the signs and exponents of
  `es` equal those of `ds`;
- `exp_p`, `exp_q`: the exponents are exchanged, i.e. `t^es_p = t^ds_{p+1}` and
  `t^es_{p+1} = t^ds_p`;
- `par`: `(-1)^ε = χ^ds_p(-1) χ^ds_{p+1}(-1)`, so the nonzero block modes of `ds` lie in
  the parity class of `ε`;
- `sym : IsSymmetric ε σ μ`, that is `μ(-k) = σ μ(k)` on the parity class;
- `sign_p`, `sign_q`: `(-1)^(e^es_p) = χ^ds_p(-1) σ` and `(-1)^(e^es_{p+1}) = χ^ds_{p+1}(-1) σ`;
- `induced_off`: every induction block of `es` at a position `i ≠ p` is also an induction
  block of `ds` at `i`, and is disjoint from `{p, p + 1}` (`p + 1 < i` or `i + 1 < p`);
- `induced_p`: if `es` has an induction block `d` at `p`, then `μ_j = 0` for `j` in the
  parity class with `|j| < |d.weight|`.

Lemmas in the namespace `IsBlockFrobData`, for `h : IsBlockFrobData n ds es p ε σ μ`:

- `neg_one_pow_positionSign_off`: off the block, `(-1)^(positionSign n es i) = χ^ds_i(-1)`.
- `hsign`: the sign matrices act on `ℓ_μ` by the signs of `es`. This is
  `blockJacquet_hsign` of module `RealBlockJacquetFunctional`, applied to the fields.
- `par_target hσ`: if `σ² = 1`, the modes of `es` on the block also lie in the parity class
  of `ε`.
- `frobFun_mem f`: the Frobenius function
  `frobFun (realStandardRep n ds) ℓ_μ (shiftedExponent n es) (positionSign n es) f` lies in
  `K(es)`. Proof: it lies in the principal series of the Frobenius characters, which is the
  principal series of the position characters of `es` (`principalSeries_posChar_shiftedExponent`),
  and it is `O(n)`-finite (`frobFun_mem_kFiniteVectors`). The Fourier conditions of `es` are
  checked on `O(n)` (`mem_realStandardModule_of_unitaryCompact`). At the block `p`, on `O(n)`,
  `Φ_j` of the Frobenius function is `μ_j Φ_j(f)`
  (`blockFourierCoefficient_frobFun`). This vanishes by `induced_p` on the parity class, and
  by parity off it. At a disjoint block `i`, the coefficient vanishes on `O(n)`
  (`blockFourierCoefficient_frobFun_eq_zero`) because the coefficients of `f` vanish there.
- `isRealJacquetFunctional hrec`: given
  `hrec : IsRecurrent (t^ds_p - t^ds_{p+1} + 1) ε μ`, `ℓ_μ` is a real Jacquet functional with
  the `ρ`-shifted exponents `shiftedExponent n es` and the signs `positionSign n es`. This is
  `isRealJacquetFunctional_blockJacquet` of module `RealBlockJacquetFunctional`; the
  exponent conditions are the fields `exp_off`, `exp_p`, `exp_q` after unfolding the shift.

### The map

- `blockFrobMap h : K(ds) →ₗ[ℂ] K(es)` is the corestriction of
  `frobLin (realStandardRep n ds) ℓ_μ (shiftedExponent n es) (positionSign n es)` to `K(es)`,
  using `frobFun_mem`.
- `blockFrobMap_apply_coe`: as a function on `GL_n(ℝ)`, `blockFrobMap h f` is that Frobenius
  function (by `rfl`).
- `blockFrobMap_apply_of_mem f hg`: for `g ∈ O(n)`,
  `blockFrobMap h f (g) = (2π)⁻¹ Σᶠ_i μ_i Φ_i(f)(g)`.
- `blockFourierCoefficient_blockFrobMap f hk j` (**multiplier on `O(n)`**): for `k ∈ O(n)`,
  `Φ_j(blockFrobMap h f)(k) = μ_j Φ_j(f)(k)`.
- `blockFrobMap_rightTranslation k f`: for `k` in the unitary group,
  `blockFrobMap h (realStandardRep n ds k f) = realStandardRep n es k (blockFrobMap h f)`.
  This holds for every `μ` and follows from `frobFun_rightTranslation`.
- `blockFrobMap_rightDerivative h hrec X f`: under `hrec`, the map commutes with the right
  derivative `realStandardLie (1 ⊗ₜ X)` along every real matrix `X`
  (`frobFun_rightDerivative`, with `isRealJacquetFunctional hrec`).
- `mk_rightTranslation_eq`, `mk_rightDerivative_eq`: the right translate and the right
  derivative of `f ∈ K(ds)`, packaged as elements of `K(ds)` with a membership proof, are
  `realStandardRep n ds k f` and `realStandardLie n ds (1 ⊗ₜ X) f`.
- `blockFrobMap_mk_rightTranslation`, `blockFrobMap_mk_rightDerivative`: the two previous
  commutation results in the packaged form used by `IsRealIntertwinerModulo`.
- `isRealIntertwinerModulo_blockFrobMap h hrec M` (**intertwiner**): under `hrec`,
  `IsRealIntertwinerModulo n ds es M (blockFrobMap h)` holds for every submodule `M` of
  `K(es)` (module `RealRankOneStepFiltration`). The membership witnesses come from
  `rightTranslation_mem_kFiniteFunctions_realStandardModule` and
  `rightDerivative_mem_kFiniteFunctions_realStandardModule`. The differences are `0`, hence
  in `M`.

### Uniqueness and composites

- `eq_of_blockFourierCoefficient_eq hp hfg`: let `p + 1 < n`, and let `f, g ∈ K(es)` have
  `Φ_j(f)(k) = Φ_j(g)(k)` for all `j` and all `k ∈ O(n)`. Then `f = g`. This holds for any
  list `es`. Proof: on `O(n)` both functions are the finite sums of their block Fourier
  coefficients (`eq_finsum_blockFourierCoefficient`, module `RealBlockFourierFinite`), so
  they agree on `O(n)`. Two functions of a principal series that agree on `O(n)` are equal
  (`eq_of_eqOn_unitaryCompact_of_mem_principalSeries`, module
  `RealStandardModuleAdmissible`).
- `blockFrobMap_blockFrobMap_eq h h' f hf`: let `h : IsBlockFrobData n ds es p ε σ μ` and
  `h' : IsBlockFrobData n es ds p ε σ' μ'`. Suppose that, for every `j` in the parity class
  with `μ'_j μ_j ≠ 1`, `Φ_j(f)` vanishes on `O(n)`. Then
  `blockFrobMap h' (blockFrobMap h f) = f`. Proof: apply the uniqueness lemma. The
  coefficients of the composite on `O(n)` are `μ'_j μ_j Φ_j(f)` by the multiplier lemma
  applied twice. Off the parity class, `Φ_j(f)` vanishes by parity
  (`blockFourierCoefficient_eq_zero_of_not_even`, module `RealBlockJacquetFunctional`).

### Lists `pre ++ ws ++ post`

- `IsBlockFrobData.of_mid hn hws hws' hexp0 hexp1 hpar hsym hsign0 hsign1 hind` gives
  `IsBlockFrobData n (pre ++ ws ++ post) (pre ++ ws' ++ post) (realRank pre) ε σ μ`. The
  lists `pre` and `post` are arbitrary. The hypotheses are:
  - `realRank (pre ++ ws' ++ post) = n` and `realRank ws = realRank ws' = 2`;
  - the exponents of `ws'` at `0, 1` are those of `ws` at `1, 0`;
  - `(-1)^ε = χ^ws_0(-1) χ^ws_1(-1)` and `IsSymmetric ε σ μ`;
  - `(-1)^(e^ws'_0) = χ^ws_0(-1) σ` and `(-1)^(e^ws'_1) = χ^ws_1(-1) σ`;
  - `μ` vanishes on the parity class below the weight of an induction block of `ws'` at `0`.

  Proof: the fields at `p, p + 1` follow from the `*_mid` lemmas of module
  `RealBlockPositionData`, and those off the block from the `*_of_not_mid` lemmas. An
  induction block of `pre ++ ws' ++ post` before `p` ends before `p`
  (`lt_of_realInducedBlockAt_of_lt`). None starts at `p + 1`
  (`realInducedBlockAt_one_of_realRank_eq_two`), and one after `p + 1` starts at or past
  `p + 2`.
