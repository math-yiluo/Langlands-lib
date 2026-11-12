# The closed dominant chamber of the actual relative Weyl group

Module `Langlands.BruhatTits.Cartan.RelativeWeylChamber`.

This helper module supports the proof of
`Langlands.BruhatTits.Cartan.AvailableCartanStatement` in
`AvailableCartanProof`. It proves two standard facts about the closed
dominant chamber of a relative root system, for the Library's actual
objects.

## Setting

Fix a field `k` and an actual homomorphism `i : T → G` of group schemes over
`Spec k`. The real cocharacter space `V(T) = ℝ ⊗ X_*(T)` carries the
published action of the actual relative Weyl group
`relativeWeylGroup i = N(k)/Z(k)` (`relativeWeylRealAction`). The pairing
`eval T χ` of a character with `V(T)` is the scalar extension of the lattice
pairing.

- `evalAt T v` packages `χ ↦ eval T χ v` as an additive map. The lemmas
  `eval_add_left`, `eval_neg_left`, `eval_sub_left`, `eval_zsmul_left` and
  `eval_nsmul_left` record additivity in the character.
- `IsDominantVector i ν v` means `0 ≤ eval T α v` for every
  `α ∈ positiveRelativeRoots i ν`, the relative roots with
  `0 < ⟨α, ν⟩`. This is the chamber of the corrected KP (5.2.1)/(5.2.2).

## Results

`isDominantVector_of_simple`: if every simple relative root is nonnegative on
`v`, then `v` is dominant. A positive root that is not simple is, by the
Library's definition of `simpleRelativeRoots`, a sum of two positive roots.
Each summand has strictly smaller positive integer pairing with `ν`, so
induction on that pairing gives nonnegativity.

`eval_relativeWeyl_smul`: `eval T χ (w • v) = eval T (w⁻¹ χ) v`, where `w⁻¹`
acts by the published `schemeWeylCharacterAction`. On representatives this is
the published `eval_normalizer_smul`.

The remaining results assume a Coxeter system `cs` on `relativeWeylGroup i`,
labelled by the simple roots, satisfying the published
`IsRelativeWeylCoxeterRealization i ν cs`. Its first three clauses are used:
the integral reflection formula `s_a χ = χ - f(χ) a` with `f(a) = 2`, the
permutation of positive roots other than `a` and `2a` by `s_a`, and the
length criterion `ℓ(w) < ℓ(w s_a) ↔ w a > 0`.

- `coxeterSimple_apply_self`: `s_a a = -a`.
- `coxeterSimple_smul_eq`: on a split torus, if `a` vanishes on `v` then
  `s_a • v = v`. Every character takes the same value on both vectors by the
  reflection formula, and the published `eq_zero_of_eval_eq_zero` separates
  vectors of `V(T)`.
- `neg_mem_positive_of_isRightDescent`: if `a` is a right descent of `w`, then
  `-(w a)` is a positive root. Here `-(w a) = (w s_a) a` is a root, and
  genericity excludes a zero pairing.
- `relativeWeyl_smul_eq_of_isDominantVector` (uniqueness): if `v` and `w • v`
  are both dominant then `w • v = v`. The proof is strong induction on
  `ℓ(w)`. For a right descent `a`, dominance of `w • v` at the positive root
  `-(w a)` gives `a(v) ≤ 0`. Dominance of `v` gives `a(v) ≥ 0`. Hence `s_a`
  fixes `v`, so `w • v = (w s_a) • v` with `ℓ(w s_a) < ℓ(w)`.
- `exists_relativeWeyl_smul_isDominantVector` (existence): every orbit meets
  the dominant cone. The proof is strong induction on the number of positive
  roots negative on `v`; this set is finite because the relative roots are. If
  no simple root is negative on `v`, the previous lemma applies. Otherwise
  choose a simple `a` with `a(v) < 0`. The map `β ↦ s_a β` sends the positive
  roots negative on `s_a • v` injectively into the positive roots negative on
  `v`, other than `a`. Indeed `β = a` and `β = 2a` are excluded because
  `s_a a = -a`, the other positive roots stay positive, and `s_a β = a` would
  force `β = -a`. So the count drops.

The wrappers `relativeWeyl_smul_eq_of_isDominantVector_of_reductive` and
`exists_relativeWeyl_smul_isDominantVector_of_reductive` take a connected
reductive `G`, a maximal split torus `i` and a generic `ν`. They obtain
the Coxeter realization from the published theorem
`Langlands.GroupScheme.relativeWeylCoxeter`, and finiteness from
`IsSplitTorus.finite_relativeRoots`.

## Provenance

This is internal, derived content: the standard fact that the closed Weyl
chamber is a fundamental domain for the Weyl group, together with the existence
half. KP use the fundamental-domain property without proof in the proof of
Theorem 5.2.1 (printed p.188 / PDF p.219 of
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`). Both proofs here are
written from scratch on the published Coxeter realization. They cover rank
zero and nonreduced relative root systems.
