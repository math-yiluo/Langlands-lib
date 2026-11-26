# Separation, completeness and off-diagonal blocks of the endomorphism filtration

Module `Langlands.BushnellKutzko.SplitObstructionLattice`. It holds general facts on the
filtration `𝔓^n = End^n_{𝔬_F}(𝓛)` of `A = End_F(V)`, where `𝓛` is an `𝔬_F`-lattice chain
(`LatticeChain 𝒪[F] F V`) and `F` is a nonarchimedean local field. They serve the proof of
Bushnell–Kutzko (1993), (2.3.12), in `SplitObstructionProof`. They are standard facts about
lattice chains, used in the source without separate statement.

## Contents

- `SplitObstruction.exists_mem_endFiltration`: every endomorphism lies in some `𝔓^k`.
- `SplitObstruction.eq_zero_of_forall_mem` and `SplitObstruction.eq_zero_of_forall_ge_mem`:
  an endomorphism lying in every `𝔓^k`, or in every `𝔓^{k₀+k}` with `k ≥ 0`, is zero.
  Both lemmas and the previous one come from part (5) of the published
  `radicalFiltration`: for `x ≠ 0` the set `{n : x ∈ 𝔓^n}` is nonempty and bounded above.
- `SplitObstruction.telescope_mem`: if `f (k+1) − f k ∈ 𝔓^{c+k}` for all `k`, then
  `f (k+m) − f k ∈ 𝔓^{c+k}`.
- `SplitObstruction.exists_limit` (completeness): for `f : ℕ → A` with `f k ∈ 𝔓^c` and
  `f (k+1) − f k ∈ 𝔓^{c+k}` there is `L ∈ 𝔓^c` with `L − f k ∈ 𝔓^{c+k}` for all `k`.
  `𝔓^c` is a finite `𝒪[F]`-module (`LatticeChain.fg_endFiltration`). So it is
  `𝓂[F]`-adically complete by `IsAdicComplete.of_finite_of_isNoetherianRing`, from the
  completeness `IsAdicComplete 𝓂[F] 𝒪[F]` in Mathlib. The proof identifies `𝓂[F]^n • 𝔓^c`
  with `𝔓^{c+n·e}` (`e` the period, via `LatticeChain.uniformizer_pow_end_mem_iff`). It then
  takes the limit of the subsequence `f (n·e)`.
- `SplitObstruction.offDiagonal ε₁ ε₂`: the `F`-subspace `{x : ε₁ x ε₂ = x}` of `A`. For
  complementary idempotents this is the block `ε₁ A ε₂ = Hom_F(V², V¹)`, where `Vⁱ = εᵢ V`.
- `SplitObstruction.blockFiltration 𝓛 ε₁ ε₂ i`: the `𝒪[F]`-module `𝔓^i ∩ ε₁ A ε₂`
  (`mem_blockFiltration`, `blockFiltration_antitone`).
- `SplitObstruction.blockFiltration_surjective` (Nakayama's lemma): let `D : A →ₗ[F] A` and
  `r : ℤ`. Suppose every `y ∈ 𝔓^{i−r} ∩ ε₁Aε₂` is `D x` modulo `𝔓^{i+1−r} ∩ ε₁Aε₂` for some
  `x ∈ 𝔓^i ∩ ε₁Aε₂`. Then every `y ∈ 𝔓^{j−r} ∩ ε₁Aε₂` equals `D x` for some
  `x ∈ 𝔓^j ∩ ε₁Aε₂`. Iterating the hypothesis one period gives
  `M_{j−r} ≤ D(M_j) + 𝓂[F] · M_{j−r}`. Mathlib's
  `Submodule.le_of_le_smul_of_le_jacobson_bot` applies, since `M_{j−r}` is finitely
  generated (`Submodule.FG.of_le`). This is the "standard completeness argument" of the
  proof of (2.3.15), printed p. 63, in the form of Nakayama's lemma.
