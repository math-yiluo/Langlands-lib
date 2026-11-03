# Projectivity from dominated factorizations

This module proves that a countably generated module with dominated factorizations is
projective. With the results of `Langlands.CommutativeAlgebra.LocallySplit.Domination`, it
follows that a countably generated flat module which becomes locally split after a faithfully
flat base change is projective. This is the module-theoretic step of the proof of
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project, Tag 05FT).
Everything is in the namespace `Langlands.CommutativeAlgebra`.

## Provenance

The statements and proofs are internal to this project; Worker 928 wrote them. Worker 281 and
Worker 928 agreed on the final theorem `projective_of_locallySplit_baseChange` as the interface
between the geometric and the module-theoretic parts of the 05FT proof. The route is a
countable telescoping argument. It plays the role of Stacks Lemma 10.93.1 (Tag 059X: a flat,
Mittag-Leffler, countably generated module is projective) and of Stacks Lemma 10.95.1
(Tag 05A5: the Mittag-Leffler property descends along faithfully flat ring maps). The Lean
development does not use any
Mittag-Leffler notion; it uses only the dominated factorizations of the `Domination` module. The
transpose trick below is a concrete instance of Stacks Lemma 10.88.5 (Tag 059D): a domination
whose source has finitely presented cokernel is a factorization.

Throughout, `R : Type u` is a commutative ring and `M : Type v` an `R`-module. Dominations in
this module are tested against `R`-modules in universe `u`, the universe of `R`.

## Results

### `exists_eq_comp_of_forall_sum_smul_eq_zero` (transpose trick)

Let `ι`, `κ`, `μ` be finite types in `Type` and let `s : (ι → R) →ₗ[R] (κ → R)` and
`t : (ι → R) →ₗ[R] (μ → R)`. Assume that for every `R`-module `N : Type u` and every
`ν : ι → N`, if `∑ i, s (e i) j • ν i = 0` for all `j`, then `∑ i, t (e i) k • ν i = 0` for
all `k`, where `e i := Pi.single i 1`. Then `t = U ∘ₗ s` for some
`U : (κ → R) →ₗ[R] (μ → R)`.

*Proof.* Let `W ⊆ R^ι` be the span of the rows `i ↦ s (e i) j` of `s`. Apply the hypothesis to
`N := R^ι ⧸ W` and `ν i :=` the class of `e i`. Then `∑ i, s (e i) j • ν i` is the class of the
`j`-th row, which is zero. Hence `∑ i, t (e i) k • ν i`, the class of the `k`-th row of `t`,
vanishes, so every row of `t` is a combination `∑ j, d k j • (row j of s)`. Then
`U := Matrix.mulVecLin (Matrix.of d)` works; this is checked on the basis vectors
(`LinearMap.pi_ext'`).

### `DominatedChain R M`

A structure consisting of:

- lengths `n : ℕ → ℕ` and tuples `x l : Fin (n l) → M`;
- coefficients `T l : Fin (n l) → Fin (n (l+1)) → R` with
  `x l i = ∑ k, T l i k • x (l+1) k` (`hx`);
- `Dominates.{u} (x l) (T l)` for every `l` (`hdom`);
- exhaustion (`hexh`): for every `m : M` and `l₀`, some `l ≥ l₀` has
  `m ∈ Submodule.span R (Set.range (x l))`.

For a chain `C`, let `H l : R^(n l) → M` be the linear combination of `x l`, and let
`t l : R^(n l) → R^(n (l+1))` send `e i` to `T l i`. Lemmas:

- `H_succ_t`: `H (l+1) ∘ t l = H l`, by `hx`.
- `t_eq_zero_of_H_eq_zero`: `H l c = 0` implies `t l c = 0`. Apply the domination `hdom l` to
  `N := R` and `ν := c`, using `∑ i, x l i ⊗ₜ c i = H l c ⊗ₜ 1`.
- `exists_t_eq_comp` (stabilisation): `t l = U ∘ₗ (t (l+1) ∘ₗ t l)` for some `U`. This is the
  transpose trick for `s := t (l+1) ∘ t l` and `t l`. If `ν` is killed by all rows of `s`, then
  `∑ i, x l i ⊗ₜ ν i = 0`, because `x l i = ∑ j, s (e i) j • x (l+2) j` by `H_succ_t`. So
  `hdom l` gives `∑ i, T l i k • ν i = 0`.
- `exists_lift`: let `k : ℕ`, let `P` be an `R`-module, and let
  `u j : R^(n (k+j)) → P` be maps with `u (j+1) ∘ₗ t (k+j) = u j`. Then some
  `z : M →ₗ[R] P` satisfies `z (H (k+j) c) = u j c` for all `j`, `c`. For well-definedness,
  if `H (k+j) c = H (k+j') c'` with `j ≤ j'`, push `c` forward along the `t`'s to level `j'`;
  the difference then lies in `ker H (k+j') ⊆ ker t (k+j')`, which `u j'` kills by the
  compatibility. By exhaustion every `m` is some `H (k+j) c`, and choosing such
  representations defines `z`. Additivity and `R`-linearity follow from well-definedness.
- `exists_z`: for every `l` some `z : M →ₗ[R] R^(n (l+1))` satisfies `z ∘ H l = t l`. Define
  `w j : R^(n (l+j+1)) → R^(n (l+1))` by `w 0 = id` and `w (j+1) = w j ∘ U (l+j)`, where `U` is
  from `exists_t_eq_comp`. The family `w j ∘ t (l+j)` is compatible because
  `t (l+j) = U (l+j) ∘ t (l+j+1) ∘ t (l+j)`. Apply `exists_lift` with `k := l` and take
  `j := 0`.

### `DominatedChain.projective`

The module of a dominated chain is projective.

*Proof.* Choose `z l` as in `exists_z` and set `α l := H (l+1) ∘ z l : M → M`. The ranges of
the `H l` increase, `α l` fixes every element of `range (H l)` (since
`H (l+1) (t l c) = H l c`), and therefore `α (l+1) ∘ α l = α l`. Let
`G := Π₀ k : ℕ, R^(n (k+1))` (a direct sum of finite free modules) and
`ψ : G → M` the sum of the maps `H (k+1)` (`DFinsupp.lsum`). For `K : ℕ` define the telescoping
maps

  `φ K := single 0 ∘ z 0 + ∑ k < K, single (k+1) ∘ z (k+1) ∘ (id - α k) : M → G`.

By induction, `ψ ∘ φ K = α K`, because `α K + α (K+1) ∘ (id - α K) = α (K+1)`. If `m` lies in
`range (H L)`, then `φ K m = φ L m` for all `K ≥ L`, because `(id - α K) m = 0` for `K ≥ L`.
By this stabilisation the maps `φ j ∘ H j` are compatible, and `exists_lift` (with `k := 0`)
gives `Φ : M → G` with `Φ (H j c) = φ j (H j c)`. For `m = H j c`,
`ψ (Φ m) = α j m = m`. So `ψ ∘ Φ = id`, and `M` is a direct summand of `G`, hence projective
(`Module.Projective.of_split`).

### `DominatedChain.nonempty_of_hasDominatedFactorizations`

If `HasDominatedFactorizations.{u} R M` holds and `g : ℕ → M` has
`Submodule.span R (Set.range g) = ⊤`, then a dominated chain exists.

*Proof.* Define tuples recursively: the `0`-th tuple is empty, and the `(l+1)`-st tuple is the
`y` of a chosen dominated factorization `(g l, x l) = A y` of the tuple `x l` with `g l`
prepended (`Matrix.vecCons`). Take `T l` to be the rows of `A` for the entries of `x l`.
Domination of `x l` by `T l` follows from domination of `(g l, x l)` by `A`, tested with `ν`
extended by `0` at the position of `g l`. For exhaustion, `g l` lies in the span of the
`(l+1)`-st tuple, the spans increase, and their supremum contains `span (range g) = ⊤`. A
directed supremum of submodules is their union.

### Main theorems

- `projective_of_hasDominatedFactorizations`: if some countable `s : Set M` has
  `Submodule.span R s = ⊤` and `HasDominatedFactorizations.{u} R M` holds, then
  `Module.Projective R M`. Enumerate `insert 0 s` (countable and nonempty) as the range of a
  sequence `g`, and apply the two previous results.
- `projective_of_locallySplit`: a countably generated `M` with `LocallySplit R M` is
  projective, by `LocallySplit.hasDominatedFactorizations`.
- `projective_of_locallySplit_baseChange`: let `R`, `R'`, `M` be in arbitrary universes, with
  `R'` a faithfully flat `R`-algebra (`Module.FaithfullyFlat R R'`) and `M` a flat `R`-module.
  If `M` is countably generated (some countable `s : Set M` has `Submodule.span R s = ⊤`) and
  `LocallySplit R' (R' ⊗[R] M)` holds, then `Module.Projective R M`. The proof combines
  `LocallySplit.hasDominatedFactorizations` over `R'`,
  `hasDominatedFactorizations_of_baseChange` (with test universe that of `R`) and
  `projective_of_hasDominatedFactorizations`.

`projective_of_locallySplit_baseChange` depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
