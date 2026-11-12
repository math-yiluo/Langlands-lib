# Radical averages contract uniformizer eigenvalues on radical coinvariants

Module `Langlands.Representation.Derivative.MirabolicRadicalContraction`.

This helper module proves the analytic core of Bernstein, *P-invariant distributions
on GL(N) and the classification of unitary representations of GL(N)
(non-archimedean case)*, Lie Group Representations II, LNM 1041 (1984), §7.3–7.4
(PDF pp. 33–34). Bernstein phrases the argument with sheaves on the radical; the
Lean proof below uses only averages over compact open subgroups of the radical.

## Main theorem

`Langlands.Derivative.Mirabolic.norm_lt_one_of_radical_eigen T m ρ`: let `ρ` be a
smooth representation of the mirabolic group `P_(m+2) = mirabolic (m + 1) F` on a
complex vector space `V`, unitarizable in the sense of `IsUnitarizable` (an invariant
positive definite Hermitian form `b`), and with no nonzero vector fixed by the whole
radical `N = radical (m + 1) F ≅ F^(m+1)`. Let `z = levi (scalar ϖ)`, the Levi
element `diag(ϖ, …, ϖ, 1)` built from the chosen uniformizer unit
`LocalFactor.PadicAbelian.uniformizerUnit T`. If `y ∉ relations ρ N 1` (its class in
the `N`-coinvariants is nonzero) and `ρ z y - c • y ∈ relations ρ N 1` (that class is
a `c`-eigenvector of `z`), then `‖c‖ < 1`.

## Auxiliary lemmas

- `re_inner_self_eq_orbitMean_add`: for a form invariant under `σ` and a vector `v`
  with finite orbit, `re ⟪v, v⟫ = re ⟪a, a⟫ + re ⟪v - a, v - a⟫` where `a` is the
  orbit mean. The linear form `w ↦ ⟪a, w⟫` is `σ`-invariant because `a` is
  `σ`-fixed, so it vanishes on `v - a` (`sub_orbitMean_mem`), giving orthogonality;
  expanding `⟪a + (v - a), a + (v - a)⟫` gives the identity.
- `re_inner_smul_self`: `re ⟪r x, r x⟫ = ‖r‖² re ⟪x, x⟫`.
- `eq_zero_of_re_inner_self_eq_zero`: definiteness, using that `⟪x, x⟫` is real.
- `uniformizer_mul_mem_additiveLattice` and `uniformizer_inv_mul_mem_additiveLattice`:
  multiplication by `ϖ` maps the additive lattice of level `k + 1` into that of
  level `k`, and multiplication by `ϖ⁻¹` maps level `k` into level `k + 1`, by the
  valuation `v(ϖ) = exp(-1)`.
- `levi_scalar_conjugate_radicalElement`: `levi (scalar a)` conjugates the radical
  element with coordinates `v` to the one with coordinates `a • v`.

## Proof of the main theorem

Let `S k = radicalBox T m k` (compact open, increasing, exhausting `N`) and let
`A k = characterAverage … (S k)` be the average over `S k` for the trivial character.
The proof establishes:

1. `A k x` is `S k`-fixed, `A k` is the identity on `S k`-fixed vectors, `A k`
   absorbs translations by `S k`, and `x - A k x ∈ relations ρ N 1`.
2. Nesting: `A (k + 1) (A k x) = A (k + 1) x`, since `A k` kills `x - A k x` and so
   does the larger average (`characterAverage_eq_zero_of_le`).
3. Box shift: `z S(k+1) z⁻¹ ⊆ S k` and `z⁻¹ S k z ⊆ S(k+1)` (the lattice lemmas and
   the conjugation formula). Hence `ρ z (A (k + 1) x)` is `S k`-fixed, so it is
   fixed by `A k`; and `A k ∘ ρ z` kills every `x - ρ u x` with `u ∈ S(k+1)`, so it
   kills `x - A (k + 1) x`. Together: `ρ z (A (k + 1) x) = A k (ρ z x)`.
4. With `Q x = re b(x, x)`, invariance gives `Q (ρ g x) = Q x`, and the orthogonality
   lemma applied to the `S k`-orbit gives `Q x = Q (A k x) + Q (x - A k x)`.

Suppose `‖c‖ ≥ 1`. Since `ρ z y - c • y` is a relation,
`eventually_characterAverage_eq_zero` gives `k₀` with `A k (ρ z y - c • y) = 0` for
all `k ≥ k₀`. For such `k`, step 3 gives `ρ z (A (k + 1) y) = c • A k y`, so
`Q (A (k + 1) y) = ‖c‖² Q (A k y)`. Applying step 4 at level `k + 1` to `A k y` and
using nesting,
`Q (A k y) = ‖c‖² Q (A k y) + Q (A k y - A (k + 1) y)`. Both terms on the right are
nonnegative and `‖c‖² ≥ 1`, so `Q (A k y - A (k + 1) y) = 0`, hence
`A (k + 1) y = A k y`. Thus `A k y = A k₀ y` for all `k ≥ k₀`, and this vector is fixed
by every `S k`, hence by all of `N`. By hypothesis it is `0`, so
`y = y - A k₀ y ∈ relations ρ N 1`, contradicting the hypothesis on `y`.
