# The prime-to-`p` quotient of a character group

Author: Worker 60 (Task 7805). Module
`Langlands.GroupScheme.Trigonalizable.PrimeToPart`, namespace
`Langlands.GroupScheme.TrigonalizableExtensionSplit.PrimeToPart`.

For a prime `p`, an integer `e` and a character group `Λ`, this module forms a
quotient `Λ ⧸ K_e` of `Λ` that is killed by `e` and has no `p`-torsion. If
moreover `p ∤ e` and `e` kills the prime-to-`p` torsion of `Λ`, then that
torsion injects into `Λ ⧸ K_e`. Such an `e` exists when `Λ` is finitely
generated (`exists_exponent`).

The quotient map of character groups induces
`ι₁ = Diagonalizable.restrictMap (QuotientAddGroup.mk' K_e) : D(Λ ⧸ K_e) ⟶ D(Λ)`.
It is the inclusion of a closed diagonalizable subgroup (by the Library's
`Diagonalizable.isClosedImmersion_restrictMap`, as used in
[`ExtensionSplitPerfectSmooth`](ExtensionSplitPerfectSmooth.md)), not a
quotient of `D(Λ)`. When `Λ` is finitely generated and `p ∤ e`, the group
`Λ ⧸ K_e` is finite of order prime to `p` (`finite_and_coprime_card`), so
over a field of characteristic `p` this subgroup is finite étale. This module
proves neither closedness nor étaleness; finiteness and the order are proved
by `finite_and_coprime_card`. `relativeSolvable` has no finite-generation
hypothesis.

Over a perfect field of characteristic `p`, assuming `p ∤ e` and that `e`
kills the prime-to-`p` torsion of `Λ`, the module proves that `ι₁` satisfies
`RelativeSolvable` (from [`RelativeTower`](RelativeTower.md)) for every closed
subgroup of `𝔾ₐ` and every character whose weight action preserves it.

## Lattice part

`p : ℕ` with `[Fact p.Prime]`, and `Λ` an additive commutative group.

- `primeToTorsion p Λ`: the subgroup of elements killed by some positive
  integer prime to `p`. `mem_primeToTorsion` unfolds membership.
- `exists_exponent` (for `[AddGroup.FG Λ]`): some `e > 0` with `p ∤ e` kills
  `primeToTorsion p Λ`. The subgroup is finitely generated (`Λ` is
  Noetherian as a `ℤ`-module), and `e` is the product of the orders of the
  generators.
- `saturation p Λ e`: the subgroup `K_e = {x | ∃ a y, p^a • x = e • y}`, the
  `p`-saturation of `e • Λ`.
- `eq_zero_of_p_smul`: `Λ ⧸ K_e` has no `p`-torsion.
- `e_smul_eq_zero`: `Λ ⧸ K_e` is killed by `e`.
- `eq_zero_of_mem_saturation`: if `p ∤ e` and `e` kills
  `primeToTorsion p Λ`, then `primeToTorsion p Λ ∩ K_e = 0`. If `w` has order
  dividing `m'` (prime to `p`) and `p^a • w = e • ν`, then `ν` is prime-to-`p`
  torsion, so `p^a • w = 0`; Bezout for `p^a` and `m'` gives `w = 0`.
- `finite_and_coprime_card` (for any `M : Type*` with `[AddCommGroup M]` and
  `[AddGroup.FG M]`): if `e > 0`, `p ∤ e` and `e • x = 0` for all `x : M`,
  then `Finite M` and `Nat.Coprime (Nat.card M) p`. `M` is a finitely
  generated torsion group, hence finite
  (`AddCommGroup.finite_of_fg_isAddTorsion`). If `p` divided its order,
  Cauchy's theorem (`exists_prime_addOrderOf_dvd_card'`) would give an
  element of order `p`, and `p` would divide `e`. Applied to `M = Λ ⧸ K_e`
  (killed by `e`, by `e_smul_eq_zero`), it shows that `Λ ⧸ K_e` is finite of
  order prime to `p` when `Λ` is finitely generated and `p ∤ e`.

## Character values

`k` a field, `evalCharacter (CommRingCat.of k) Λ m` the character of `D(Λ)`
given by `m : Λ`.

- `charValue_evalCharacter`: the value of this character at a point is the
  unit `characterPointsEquiv` assigns to `m`.
- `charValue_evalCharacter_add`, `_nsmul`, `_zero`: values are multiplicative
  in `m`.
- `eq_zero_of_charValue_evalCharacter`: if the character of `m` takes the
  value `1` at every point, then `m = 0` (by the Library's
  `evalCharacterAddHom_bijective` and `characterLattice.ext_points`).
- `charValue_restrictMap`: for `g : Λ →+ Λ₁`, the value of the character of
  `m` at `ι(z)`, where `ι = Diagonalizable.restrictMap (CommRingCat.of k) g`,
  is the value of the character of `g m` at `z` (the Library's
  `Diagonalizable.pointsEquiv_restrictMap`).

## `relativeSolvable`

Let `k` be perfect with `[CharP k p]`, `p ∤ e`, `e` killing
`primeToTorsion p Λ`, `ι₁ = restrictMap (QuotientAddGroup.mk' K_e)`, `a` a
closed subgroup of `𝔾ₐ` and `χ` a character whose weight action preserves the
range of `a`. Then `RelativeSolvable ι₁ a χ`.

Write `χ` as the character of `l : Λ`, `g` for the quotient map and `f` for
the closed polynomial of `a`, assumed nonzero. By
`PerfectCorrection.eq_zero_or_eq_pow_of_coeff_ne_zero`, the degree of `f` is
`p^s`, and every other exponent with nonzero coefficient is `0` or a power of
`p`.

1. If `χ(ι₁ z)^(p^s) = 1` everywhere, then `g(p^s • l) = 0`, so `g l = 0`
   because `Λ ⧸ K_e` has no `p`-torsion. Hence `χ ∘ ι₁ = 1`.
2. Assume `χ ∘ ι₁ = 1`, that is, `g l = 0`. If all coefficients of `f` below
   the leading one vanish, then `f = X^(p^s)`, which is surjective on the
   perfect field `k` (`iterateFrobeniusEquiv`). Otherwise some coefficient at
   `p^v` with `v < s` is nonzero. Stability of the range of `a` gives
   `χ^(p^v) = χ^(p^s)` (`PerfectCorrection.charValue_pow_eq_of_coeff_ne_zero`),
   so `w = p^v • l` satisfies `(p^(s-v) - 1) • w = 0`. Hence `w` is
   prime-to-`p` torsion; it lies in `K_e` because `g l = 0`. By
   `eq_zero_of_mem_saturation`, `w = 0`, so `χ^(p^s) = 1` everywhere.

## Provenance

Internal. The closed subgroup `D(Λ ⧸ K_e)` of `D(Λ)`, which is finite étale
for finitely generated `Λ`, and the elementary lattice facts are standard.
This decomposition is not in
Milne's proof of 16.26 (`milne-2017-algebraic-groups`, printed pp.332–333),
which treats case (b) differently. It serves the proof of case (b) in
[`ExtensionSplitPerfectSmooth`](ExtensionSplitPerfectSmooth.md).
