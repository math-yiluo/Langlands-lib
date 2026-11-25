# Alternating bicharacters and projective representations (internal)

**GKT §1.2.1**, abstract part: maximal self-orthogonal subgroups (Lemma 1.3, p. 19), the extension
of `ψ` to `H(A)` (Corollary 1.4, p. 19), and the eigenvector arguments behind the irreducibility of
the induced model (Proposition 1.12, p. 23) and the uniqueness in Theorem 1.31 (p. 36).

The module `Langlands.Theta.Heisenberg.SelfDualSubgroup` holds the abstract part of the
construction of the induced models of the Heisenberg group. Everything in it is internal
(namespace `Langlands.HeisenbergGroup.Internal`) and is used by `Langlands.Theta.Heisenberg.SelfDual`
and `Langlands.Theta.Heisenberg.InducedModel`; a user of the subject should not need it.

## Content

Let `W` be an abelian group and `c : W → W → ℂ` an alternating bicharacter
(`IsAlternatingBicharacter c`: multiplicative in each variable, `c x x = 1`; hence
`c x y · c y x = 1`). The orthogonal of a set `T` is the subgroup
`{x | c(x, t)² = 1 for t ∈ T}`; taking orthogonals three times gives at most the first one. A map
`ρ : W → End(M)` is a projective representation with cocycle `c` (`IsProjectiveRep c ρ`) if
`ρ 0 = 1` and `ρ x ρ y = c(x, y) ρ(x + y)`; then `ρ x ρ y = c(x, y)² ρ y ρ x`. A function `α`
splits `c` on a subgroup `A` (`SplitsOn c A α`) if it does not vanish on `A` and
`α a α b = c(a, b) α(a + b)` there; then `a ↦ α(a)⁻¹ ρ a` is a representation of `A`.

In the application `c(x, y) = ψ(½ B(x, y))`, so that `c² = ψ ∘ B`, and `ρ x` is the action of
`(x, 0)` in a representation of the Heisenberg group with central character `ψ`.

The results, in the order of the file:

- `IsProjectiveRep.apply_average`: if `m` is fixed by `ρ u` for `u` in a subgroup `U ⊆ A` on
  which `α = 1`, and `A / U` is finite, the average `∑_{a ∈ A/U} α(a)⁻¹ ρ(a) m` is an
  `α`-eigenvector of `A`.
- `exists_eigenvector`: an invariant subspace containing a non-zero vector fixed by the
  orthogonal `U` of a set `T`, with `α = 1` on `U` and `A / U` finite, contains a non-zero
  `α`-eigenvector of `A`. If every average vanished, then for every `w` in the orthogonal of `U`
  the vectors `α(a)⁻¹ ρ(a) v` would satisfy a linear relation with coefficients the characters
  `w ↦ c(a, w)²` of the orthogonal of `U`; these characters are distinct for distinct classes of
  `A / U` (by the triple-orthogonal inclusion), so the relation is trivial by Dedekind's
  independence of characters, and `v = 0`.
- `sum_eq_zero_of_eigenvalues_ne`, `exists_eq_smul_of_mem_span`: when `A` contains its
  orthogonal, the `α`-eigenvectors of `A` in the span of the translates `ρ x e` of an
  `α`-eigenvector `e` form the line `ℂ e` (the translate `ρ x e` is an eigenvector with eigenvalue
  `c(a, x)² α(a)`, which differs from `α` unless `x` is in the orthogonal of `A`).
- `exists_le_selfOrthogonal`: a self-orthogonal subgroup is contained in one that contains its
  orthogonal (a maximal self-orthogonal subgroup, by Zorn's lemma).
- `exists_splitsOn`: on a self-orthogonal subgroup `A` the cocycle `c` (symmetric there) is split,
  by an `α` equal to `1` on a given subgroup `L ⊆ A` on which `c = 1`. The extension of `A` by `ℂˣ`
  with cocycle `c` (`TwistedProduct`) is abelian, and the character `(l, z) ↦ z` of `L × ℂˣ`
  extends to it because `ℂˣ` is divisible, hence an injective abelian group
  (`baer_additiveUnits`).
- `translate c x`, `isProjectiveRep_translate`, `translate_indicator`: the operators
  `f ↦ (z ↦ c(z, x) f(z + x))` on functions on `W` form a projective representation with cocycle
  `c`, and `α · 1_A` is an `α`-eigenvector of `A`.

Mœglin–Vignéras–Waldspurger, *Correspondances de Howe sur un corps p-adique* (Lecture Notes in
Math. 1291, Springer 1987), chapter 2, I.3–I.5, pp. 28–31 (construction of the representation from
a closed subgroup `A = A^⊥` of `W` and a character of `A × F` extending `ψ`, and its uniqueness).

## Source and licence

Lines 70–355 of
`src/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean`
of <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65` (section
`Abstract` of namespace `GlobalTheory.Published.SvN`). The repository has no licence file; the
text is used with attribution, see
`licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `GlobalTheory.Published.SvN` → `Langlands.HeisenbergGroup.Internal`.
- Renamed: `Alt` → `IsAlternatingBicharacter` (fields `left`, `right`, `self` → `map_add_left`,
  `map_add_right`, `apply_self`), `Alt.anti` → `mul_swap`, `Alt.ne` → `ne_zero`, `Alt.sq_swap` →
  `sq_eq_one_swap`, `Alt.perp` → `orthogonal`, `Alt.perp_perp_perp` →
  `orthogonal_orthogonal_orthogonal_le` (stated as an inclusion), `Ops` → `IsProjectiveRep`
  (fields `zero`, `mul` → `apply_zero`, `apply_apply`), `Ops.eq_zero` →
  `eq_zero_of_apply_eq_zero`, `Splits` → `SplitsOn` (field `ne` → `ne_zero`), `Splits.comp` →
  `inv_smul_comp`, `average` → `IsProjectiveRep.apply_average`, `exists_eigen` →
  `exists_eigenvector`, `eq_zero_of_sum` → `sum_eq_zero_of_eigenvalues_ne`, `eigen_line` →
  `exists_eq_smul_of_mem_span`, `exists_selfDual` → `exists_le_selfOrthogonal`, `Tw` →
  `TwistedProduct`, `baer_units` → `baer_additiveUnits`, `exists_splits` → `exists_splitsOn`,
  `transl` → `translate`, `ops_transl` → `isProjectiveRep_translate`, `transl_indicator` →
  `translate_indicator`.
- New: `IsAlternatingBicharacter.mem_orthogonal`, `translate_apply`.
- Universes of `W`, `M` and of the index type of `sum_eq_zero_of_eigenvalues_ne` are arbitrary
  (the source: `Type`). The deprecated `dif_pos` is replaced by `dite_eq_left`.
- Proofs are otherwise the source's.

## Declarations

All internal: `IsAlternatingBicharacter` and its lemmas, `IsProjectiveRep`, `SplitsOn`,
`exists_eigenvector`, `exists_eq_smul_of_mem_span`, `exists_le_selfOrthogonal`,
`exists_splitsOn`, `translate`.

## Dependencies

Mathlib only: `Algebra.Group.MinimalAxioms`, `Algebra.Module.CharacterModule`,
`Analysis.Complex.Polynomial.Basic`, `GroupTheory.Divisible`, `LinearAlgebra.Dual.Lemmas`,
`LinearAlgebra.LinearIndependent.Basic`, `Order.Zorn`.
