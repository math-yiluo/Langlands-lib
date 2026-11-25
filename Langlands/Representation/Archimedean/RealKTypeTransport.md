# Transporting `O(n)`-finite functions by left multiplication on `O(n)`

Module `Langlands.Representation.Archimedean.RealKTypeTransport` (namespace
`Langlands.Archimedean.RealKTypeTransport`).

## Main results

* `surjective_of_injective_induced_character c d`: let `c : RealCharacterData` (a character
  `χ` of `GL_1(ℝ)`) and `d : ComplexCharacterData` (an induction block `D`). Every injective
  linear map `T` from the `O(3)`-finite functions of `realStandardModule 3 [induced d,
  character c]` to those of `realStandardModule 3 [character c, induced d]` that commutes with
  right translation by `O(3)` (`IsRealKEquivariant`, module `RealKTypeCount`) is surjective.
* `surjective_of_injective_character_induced c d`: the same for maps in the other direction,
  from `[character c, induced d]` to `[induced d, character c]`.

No condition on the exponents is assumed. Both theorems apply the lemma
`RealKTypeCount.surjective_of_injective`, which needs one injective `O(3)`-equivariant map in
the opposite direction. That map is `cycleMap c d` resp. `cycleInvMap c d` below. The theorems
are helpers for the `GL_3(ℝ)` filtrations (`RealCharacterInducedFiltrationStatement` and
`RealInducedCharacterFiltrationStatement`): there an intertwiner between the
two standard modules is shown to be injective, and these theorems make it bijective.

## Definitions

* `transport κ₀` (for `κ₀ ∈ Matrix.unitaryGroup (Fin n) ℝ`): the complex linear map sending
  `f : GL_n(ℝ) → ℂ` to the function `κ ↦ f(κ₀ κ)` on `O(n)` (through `Unitary.toUnits`).
* `IsSignCompatible κ₀ χ χ'` (a `Prop`): for every `a : Fin n → ℝˣ` there is
  `b : Fin n → ℝˣ` with `κ₀ · signDiagonal a = signDiagonal b · κ₀` and
  `principalSeriesCharacter ℝ n χ (sgn b) = principalSeriesCharacter ℝ n χ' (sgn a)`. Here
  `signDiagonal a` is the diagonal matrix of the signs of the `a i`. This condition makes
  `κ ↦ f(κ₀ κ)` satisfy the `O(n) ∩ B` transformation law of the principal series of `χ'`
  when `f` lies in the principal series of `χ`.
* `transportMap V W κ₀ e' hVW`: the map `f ↦ extension (shiftedExponent n e') (transport κ₀ f)`
  from `kFiniteFunctions V (unitaryCompact ℝ n)` to `kFiniteFunctions W (unitaryCompact ℝ n)`.
  `extension` is the Library's extension of a function on `O(n)` to `GL_n(ℝ)` via the Iwasawa
  decomposition (module `PrincipalSeriesExtension`). The argument `hVW` is the hypothesis that
  the map lands in `W`.
* `cycleMatrix = !![0, 0, 1; 1, 0, 0; 0, 1, 0]`, the permutation matrix `w` with
  `w e₀ = e₁`, `w e₁ = e₂`, `w e₂ = e₀`, and `cycleInvMatrix = !![0, 1, 0; 0, 0, 1; 1, 0, 0]`,
  its inverse. `cycle` and `cycleInv` are the same matrices as elements of `O(3)`.
* `cycleMap c d = transportMap _ _ cycle (realPositionExponent [induced d, character c]) _`,
  from `[character c, induced d]` to `[induced d, character c]`, and
  `cycleInvMap c d = transportMap _ _ cycleInv (realPositionExponent [character c, induced d]) _`
  in the other direction.

These are auxiliary constructions with internal provenance. None of them corresponds to a
definition of the literature.

## Lemmas and proofs

### Standard modules from `O(n)`

* `realInducedBlockAt_eq_some`: if the induction block `d` sits at position `p` of `ds`, the
  position characters at `p`, `p + 1` are `realInducedFirstCharacter d`,
  `realInducedSecondCharacter d`, and the position exponents are `t ± |m|/2` (`t` the exponent
  and `m` the weight of `d`). By induction on `ds`.
* `realPositionCharacter_exp`: `realPositionCharacter ds l (e^x) = exp(realPositionExponent ds
  l · x)`, from `realPositionCharacter_eq_signUnit_mul` and `realPositionCharacter_one`.
* `even_of_neg_one_zpow_eq`: `(-1)^j = (-1)^(M+1)` implies `j + M + 1` even.
* `mem_realStandardModule_of_unitaryCompact`: let `realRank ds = n` and let `f` lie in the
  principal series of `realPositionCharacter ds`. If, for every induction block `d` at a
  position `p` and every `|j| < |weight d|`, the block Fourier coefficient
  `blockFourierCoefficient n p j f k` vanishes at every `k ∈ O(n)`, then `f` lies in
  `realStandardModule n ds`. The standard module asks for this vanishing at every
  `g ∈ GL_n(ℝ)`. For modes `j` of the parity `j + |m| + 1` even, the Library's
  `RealBlockPropagation.blockFourierCoefficient_window_eq_zero` propagates the vanishing on
  `O(n)` to all of `GL_n(ℝ)`. Its exponent hypothesis is the computation `hδ`: the shifted
  exponents at `p` and `p + 1` differ by `|m| + 1`. For modes of the other parity,
  `RealBlockFourierFinite.blockFourierCoefficient_eq_zero_of_parity` shows that the
  coefficient vanishes everywhere, because `χ_p(-1) χ_{p+1}(-1) = (-1)^(|m|+1)`.

### The transport map

* `continuous_transport`, `finiteDimensional_transport`: `transport κ₀ f` is continuous when
  `f` is, and its right `O(n)`-translates span a finite-dimensional space when those of `f` do.
  The span is contained in the image under `transport κ₀` of the span of the right translates
  of `f`.
* `transport_signDiagonal_mul`: under `IsSignCompatible κ₀ χ χ'`, for `f` in the principal
  series of `χ`, `transport κ₀ f (signDiagonal a · κ) = χ'(sgn a) · transport κ₀ f κ`.
* `extension_transport_mem`: for `V ≤ principalSeries ℝ n χ`, under `IsSignCompatible` and the
  factorization `χ' l x = χ' l (sgn x) |x|^{e' l}`, the extension of `transport κ₀ f` is an
  `O(n)`-finite function of the principal series of `χ'`
  (`PrincipalSeriesExtension.extension_mem_kFiniteFunctions`).
* `transportMap_apply_toUnits`: `transportMap … f` takes the value `f(κ₀ κ)` at `κ ∈ O(n)`
  (`extension_unitary`).
* `transportMap_injective`: if `transportMap … f = 0`, then `f(κ₀ κ) = 0` for all `κ`, so `f`
  vanishes on `O(n)` and is `0` by `eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`.
* `transportMap_isRealKEquivariant`: if `V` is stable under right `O(n)`-translation (`hVK`),
  then `transportMap` is `IsRealKEquivariant`. The right translate of the extension is the
  extension of the right translate on `O(n)` (`rightTranslation_extension`), and
  `f(κ₀ (x k)) = (R_k f)(κ₀ x)`.
* `blockFourierCoefficient_of_transport`: if `g(κ) = f(κ₀ κ)` on `O(n)` and
  `κ₀ r_p(θ) = r_q(θ) κ₀` for all `θ`, then at `k ∈ O(n)`
  `blockFourierCoefficient n p j g k = blockFourierCoefficient n q j f (κ₀ k)`; the integrands
  agree pointwise.

### `GL_3(ℝ)`

* `cycleMatrix_mem`, `cycleInvMatrix_mem`: both matrices are orthogonal (entrywise check).
* `cycle_mul_blockRotation`, `cycleInv_mul_blockRotation`: `w r_0(θ) = r_1(θ) w` and
  `w⁻¹ r_1(θ) = r_0(θ) w⁻¹`. The entries of `r_p(θ)` are given by
  `RealBlockRotation.blockRotation_apply`; both sides are compared entrywise.
* The imported `Langlands.Archimedean.realStandardModule_le_principalSeries`
  from `RealStandardModuleFourier` supplies `realStandardModule N ds ≤ principalSeries ℝ N
  (realPositionCharacter ds)`.
* `cycle_isSignCompatible c d`: `IsSignCompatible cycle (realPositionCharacter [character c,
  induced d]) (realPositionCharacter [induced d, character c])`, with `b = (a₂, a₀, a₁)`:
  `w diag(a) = diag(a₂, a₀, a₁) w`, and both character values are
  `χ_c(sgn a₂) χ_{D,1}(sgn a₀) χ_{D,2}(sgn a₁)` (`JacquetKernel.principalSeriesCharacter_sign`).
* `cycleInv_isSignCompatible c d`: the same for `cycleInv` and the characters in the other
  order, with `b = (a₁, a₂, a₀)`.
* `cycle_landing c d`: for `f` an `O(3)`-finite function of the standard module of
  `[character c, induced d]`, the extension of `transport cycle f` is an `O(3)`-finite function
  of the standard module of `[induced d, character c]`. It lies in the principal series by
  `extension_transport_mem`. Its only induction block sits at position `0`, and its block-`0`
  coefficients on `O(3)` are the block-`1` coefficients of `f` at `w k`
  (`blockFourierCoefficient_of_transport`, `cycle_mul_blockRotation`), which vanish for
  `|j| < |m|` because `f` lies in the standard module of `[character c, induced d]`, whose
  induction block sits at position `1`. Then `mem_realStandardModule_of_unitaryCompact`
  applies.
* `cycleInv_landing c d`: the same with the roles of the positions `0` and `1` exchanged.
* `cycleMap_injective`, `cycleInvMap_injective`, `cycleMap_isRealKEquivariant`,
  `cycleInvMap_isRealKEquivariant`: instances of `transportMap_injective` and
  `transportMap_isRealKEquivariant`; the stability of the standard modules under right
  `O(3)`-translation is the Library's
  `rightTranslation_mem_kFiniteFunctions_realStandardModule`.
* `surjective_of_injective_induced_character` uses `cycleMap c d` as the opposite map in
  `RealKTypeCount.surjective_of_injective`, and
  `surjective_of_injective_character_induced` uses `cycleInvMap c d`.

## Provenance

Internal. The transport by an element of `O(n)` and the cyclic permutation on `GL_3(ℝ)` are
elementary constructions designed for the counting argument of the `GL_3(ℝ)` filtrations.
Informally, `cycleMap` shows that every `O(3)`-type occurs in the two standard modules with the
same multiplicity, because both are induced from characters of the same restriction to
`O(3) ∩ B` up to conjugation by `w`. No literature source is formalized.
