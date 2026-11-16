# Tied irreducibility from the tempered irreducibility statement

Lean module: `Langlands.Representation.Archimedean.RealTiedIrreducible`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
connects the hypothesis `RealBlockFunctional.TiedIrreducible` of the block Jacquet functional
(module `RealBlockFunctional`) with the Library statement `RealTemperedStandardIrreducibleStatement`
(module `RealTemperedIrreducibleStatement`, proof Task 7158).

Notation: `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ` and `O(N)` is `unitaryCompact ℝ N`.
`IsSignedPower ψ f` (module `PartialJacquetIntegral`) means `ψ_l(x) = ψ_l(sgn x) |x|^{f_l}`,
`ψ_l(1) = 1` and `‖ψ_l(−1)‖ = 1`, with `GramFormula.signUnit x` the sign of `x`.
`kFiniteRep V` and `kFiniteLie V` (module `PrincipalSeriesGKModule`) are right translation by `O(N)`
and the right-derivative action on the `O(N)`-finite functions of a space `V`; `principalSeriesRep`,
`principalSeriesLie` (for `V = principalSeries ℝ N ψ`) and `realStandardRep`, `realStandardLie`
(for `V = realStandardModule N ds`, module `RealStandardModuleGKModule`) are instances.
`RealJacquetFrobenius.charData e t` and `charFun e t x = (x/|x|)^e |x|^t` (module
`RealJacquetFrobeniusProof`) give the character `sgn^e |·|^t` as `RealCharacterData`.
Unprefixed names below are in the namespace `Langlands.Archimedean.RealTiedIrreducible`.

## The statement

`RealTiedIrreducibleStatement` is the implication
`RealTemperedStandardIrreducibleStatement → RealBlockFunctional.TiedIrreducible`. Spelled out:
assuming that every real standard module `realStandardModule n ds` with `realRank ds = n` whose
blocks all have the same real exponent is irreducible, for every `b`, every signed-power family
`ψ` with exponents `f`, signs `ψ_l(−1) = (−1)^{q_l}` (`q : ℕ → ℕ`) and `Re f_l = Re f_0` for
`l < b`, the `(𝔤𝔩_b(ℝ), O(b))`-module `(principalSeriesRep ℝ b ψ, principalSeriesLie ℝ b ψ)` is
irreducible. It is proved as `Langlands.Archimedean.realTiedIrreducible`.

Provenance. Derived, internal: a change of model between the principal series of a family of
characters and the standard module of the corresponding list of character blocks. No literature
statement is claimed.

## Proof

* `principalSeries_congr`: `principalSeries ℝ N χ` only depends on `χ_l` for `l < N`, because
  `principalSeriesCharacter ℝ N χ a` is a product over `i : Fin N`.
* `isIrreducible_kFinite_of_eq`: if `V = V'`, irreducibility of
  `(kFiniteRep V, kFiniteLie V)` gives irreducibility of `(kFiniteRep V', kFiniteLie V')`, whatever
  the proofs of the stability hypotheses (substitution of the equality).
* `parity q = q mod 2 ∈ Fin 2` and `charList b f q`, the list of the `b` character blocks
  `charData (parity q_l) f_l` (`l < b`), that is `sgn^{q_l} |·|^{f_l}`.
* `isCharacterList_charList`, `realRank_charList` (`= b`, by the Library's
  `realRank_map_character`), `realBlockExponent_charList` (every block has real exponent
  `Re f_i` for some `i < b`).
* `realPositionCharacter_charList`: the position character of `charList b f q` at `l < b` is
  `charFun (parity q_l) f_l` (Library `realPositionCharacter_map_character`).
* `charFun_eq`: `charFun (parity q_l) f_l = ψ_l`, by `ψ_l(x) = ψ_l(sgn x) |x|^{f_l}`, `ψ_l(1) = 1`,
  `ψ_l(−1) = (−1)^{q_l} = (−1)^{q_l mod 2}` and `x/|x| = ±1`.
* `realTiedIrreducible`: the blocks of `charList b f q` all have real exponent `Re f_0`, so the
  tempered statement gives irreducibility of its standard module. By the published
  `RealStrictCharacterLanglandsQuotient.realStandardModule_eq` (a list of character blocks has no
  Fourier conditions) and `principalSeries_congr`,
  `realStandardModule b (charList b f q) = principalSeries ℝ b ψ`, and
  `isIrreducible_kFinite_of_eq` transports irreducibility.
