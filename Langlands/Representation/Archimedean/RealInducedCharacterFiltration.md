# The induced–character filtration on `GL₃(ℝ)`

Module `Langlands.Representation.Archimedean.RealInducedCharacterFiltration` (namespaces
`Langlands.Archimedean.RealStandardFiltration` and `Langlands.Archimedean.RealInducedCharacter`).

## Main result

`RealInducedCharacter.realInducedCharacterFiltration_of_landing (hL) (hL') :
RealInducedCharacterFiltrationStatement`.

The target statement `RealInducedCharacterFiltrationStatement` is in the Library module
`RealInducedPairFiltrationReduction`. It says: let `d : ComplexCharacterData` be an induction
block and `c : RealCharacterData` a character with `Re t(d) < Re t(c)`. Then the standard
module of `[induced d, character c]` on `GL₃(ℝ)` has a filtration as in
`RealAdjacentFiltration 3 [] []`. Each graded piece is a quotient of the standard module of
`[c, d]`, or of a list with a permutation of the exponent support and a strictly larger sum of
squared weights.

The theorem assumes the two landing statements of Worker 763 (module
`RealSwapLandingStatement`, Task 7133). These are
`hL : RealSwapLandingInducedFirstStatement` and `hL' : RealSwapLandingCharacterFirstStatement`.
They are not proved in this module, so this module alone does **not** prove the target
statement. The module `RealInducedCharacterFiltrationProof` discharges both hypotheses
(by `RealSwapLandingIntegral.inducedFirst` and
`RealSwapLandingMirror.characterFirst_of_inducedFirst`) and proves the target. Apart from these
two hypotheses, the proof uses no assumption beyond Lean's standard axioms. All other inputs
are proved theorems: in the Library, in Worker 763's modules `RealSwapFLanding` and
`RealBlockTransposition`, or in the modules listed below.

This is an internal development for Task 7134. It follows the case plan of Worker 763's
mirror task 7133 (`RealCharacterInducedFiltrationStatement`). No literature statement is
formalized.

Notation. `d` has weight `m`, `ℓ = |m|` and exponent `t`. `c` has parity `ε` and exponent
`s`. `a = t + ℓ/2` (`aExp d`) and `b = t - ℓ/2` (`bExp d`).

## Weight `0`

`RealStandardFiltration.realAdjacentFiltration_induced_character_of_weight_eq_zero hC d c hw
hdc`. Assume `hC : RealCharacterPairFiltrationStatement`, `d.weight = 0` and
`Re t(d) < Re t(c)`. Then the filtration exists.

*Proof.* For weight `0` the induction block expands to the two characters
`c₁ = sgn|·|^t` and `c₂ = |·|^t` (`realBlockExpand`). The `O(3)`-finite functions of the
standard modules agree: `KF 3 [d, c] = KF 3 [c₁, c₂, c]` and
`KF 3 [c, d] = KF 3 [c, c₁, c₂]` (`kf_append_expand`, module `RealCharacterInducedWeightZero`,
Library). Work with the reformulation `realAdjacentFiltration_iff` in terms of
`HasFiltration` (Library module `RealStandardFiltration`).

1. Filter `[c₁, c₂, c]` by the pair `(c₂, c)` with `pre = [c₁]`, using `hC`.
2. The piece `[c₁, c, c₂]` is filtered again by the pair `(c₁, c)` with `post = [c₂]`. This
   gives the piece `[c, c₁, c₂]`, which is `[c, d]`, and pieces `ws' ++ [c₂]`.
3. The other pieces have the form `[c₁] ++ ws`.

In both kinds of other pieces, `ws` or `ws'` has a permuted exponent support and a positive
weight square sum. The whole list then has a permuted support `[t, t, s]` and a weight square
sum `> 0 = ` that of `[d, c]`. The steps are glued by `HasFiltration.bind`,
`HasFiltration.of_eq_pieces`, `HasFiltration.self` and `HasFiltration.congr`. At the call
site, `hC` is `realCharacterPairFiltration` (Library).

## The case split

The arithmetic lemmas `stage1_int`, `stage1_nonint`, `stage2_int`, `stage2_nonint` give the
nonvanishing conditions of the generic multipliers:

* the denominators `ε' + 2i + 1 + N ≠ 0`;
* `N ≠ ε' + 2k + 1`.

They hold when `N` is not an integer, when `N = 0`, or when `N` is an integer of the right
parity. `re_aExp` computes `Re a = Re t + ℓ/2`.

`realInducedCharacterFiltration_of_hard (hL) (hhard)` assumes `hL` and the filtration in the
hard case `hhard`: `s - a = -m'` with `m' ≥ 1` and `2m' < ℓ`. It concludes
`RealInducedCharacterFiltrationStatement`. Given `d`, `c` with `Re t < Re s`:

* `ℓ = 0`: the weight-`0` lemma.
* `s - a` is an integer `z < 0`: write `z = -m'`. Then `2m' < ℓ`, because
  `Re s = Re t + ℓ/2 - m' > Re t`. Apply `hhard`.
* `z = 0`: take `s_b = (ℓ + ε) mod 2` and `s_a = (ℓ + 1 + s_b) mod 2`. Both swaps are generic.
  `ν₁ = s - a = 0`, and `ν₂ = s - b = ℓ` has the parity of `pairParity c_b c`. Apply
  `pushforward_generic` (module `RealInducedCharacterPushforward`).
* `z = k ≥ 1`: take `s_a = (k + ε) mod 2`, so that `ν₁ = k` has the parity of
  `pairParity c_a c` and the first swap is generic. Take `s_b = (ℓ + 1 + s_a) mod 2`. Then
  `ν₂ = k + ℓ =: ℓ'` is an integer `> ℓ` with `ℓ' - 1 ≡ pairParity c_b c`. Apply
  `pushforward_reducible`.
* `s - a` not an integer: take `s_a = 0` and `s_b = (ℓ + 1) mod 2`. Both swaps are generic,
  because `s - a` and `s - b = (s - a) + ℓ` are not integers. Apply `pushforward_generic`.

## The filtration statement from the landing statements

`realInducedCharacterFiltration_of_landing hL hL'` is `realInducedCharacterFiltration_of_hard
hL` with the hard case supplied by `RealInducedCharacter.hard_filtration hL hL'` (module
`RealInducedCharacterHard`).

## Module structure

The proof is spread over five modules:

* `RealInducedCharacterMaps`: notation and the tail maps.
* `RealInducedCharacterLanding`: the mirror landing `highModes_eq_zero_mirror`.
* `RealInducedCharacterPushforward`: the generic and reducible cases.
* `RealInducedCharacterHard`: the hard case `s - a = -m'`.
* this module: the case split and the final theorem.
