# From the bimodule statement to one-sided nonvanishing of the Jacquet module

Module: `Langlands.Representation.Archimedean.ComplexJacquetBimoduleBridge`.

## Result

`Langlands.Archimedean.complexJacquetOneSided_of_bimodule` proves the implication

`ComplexJacquetBimoduleStatement.{uV} → ComplexJacquetOneSidedStatement.{uV}`.

Both sides are Library statements:

- `ComplexJacquetBimoduleStatement` (module `ComplexJacquetBimodule`) is one-sided nonvanishing
  `ℓ(𝔫)V ≠ V` for two commuting actions `ℓ`, `r` of `𝔤𝔩_n(ℂ)` on `V`, given a nonzero
  finite-dimensional subspace `E` that is stable under `ℓ(Y) - r(Yᵀ)`, is spanned by vectors
  with integer eigenvalues for every `ℓ(E_pp) - r(E_pp)`, and generates `V` under `ℓ`, where `ℓ`
  has an infinitesimal character.
- `ComplexJacquetOneSidedStatement` (module `ComplexJacquetOneSided`) is: for every irreducible
  admissible `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ, π)`, the span of the vectors `ee π 0 p q v` with
  `p < q` is not all of `V`.

This is a helper theorem, not a Library statement, and it is internal to the project. The
bimodule statement is the project's form, for `𝔤𝔩_n(ℂ)`, of Bernstein–Gelfand's theorem (J.
Bernstein and S. Gelfand, *Tensor products of finite and infinite dimensional representations
of semisimple Lie algebras*, Compositio Math. 41 (1980), Theorem 5.9), as recorded in
`ComplexJacquetBimodule.md`. This module checks that an irreducible admissible
`(𝔤𝔩_n(ℂ), U(n))`-module satisfies its hypotheses. The argument below is ours. Apart from
Mathlib, it uses only Library lemmas about `(𝔤𝔩_n(ℂ), U(n))`-modules.

## Setting

`π̃ = ComplexGenericLarge.prodAction π` is `π` transported to `𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`, written as
`Fin 2 → Matrix (Fin n) (Fin n) ℂ`. `factorHom i` is the Lie algebra inclusion `Y ↦ Pi.single i Y`.
The two actions are `ℓ = leftAct π = π̃ ∘ factorHom 0` and `r = rightAct π = π̃ ∘ factorHom 1`, so
`ℓ(E_pq) = ee π 0 p q` and `r(E_pq) = ee π 1 p q` hold by definition. They commute
(`leftAct_mul_rightAct`) because `Pi.single 0 X * Pi.single 1 Y = 0` in both orders, and
`π(x) = ℓ(x₀) + r(x₁)` for the two components of `x` (`pi_eq_left_add_right`).

## Proof

Fix a nonzero `v ∈ V` and let `E = FiniteVectors.orbitSpan ρ v`, the span of the `U(n)`-orbit
of `v`. It is finite-dimensional by the `U(n)`-finiteness in `IsComplexGKModule`, is stable
under `ρ`, and contains `v`, so `E ≠ ⊥`. The remaining hypotheses of the bimodule statement
are checked as follows.

1. **`E` is stable under `ℓ(Y) - r(Yᵀ)`** (`kappa_mem`). For skew-Hermitian `Y`, the conjugate
   of `Y` in the second factor is `-Yᵀ`, so `π(1 ⊗ Y) = ℓ(Y) - r(Yᵀ)` (`pi_skew_eq`). The
   Library lemma `skew_stable` says that a `U(n)`-stable subspace is stable under `π(1 ⊗ Y)` for
   such `Y`. A general `Y` is `A + iB` with `A = (Y - Y*)/2` and `B = -i(Y + Y*)/2` both
   skew-Hermitian, and `ℓ(Y) - r(Yᵀ)` is complex linear in `Y`.

2. **Integer joint eigenvectors span `E`** (`le_span_joint`). Let `D_p = ℓ(E_pp) - r(E_pp)`
   (`diagDiff`). By the Library lemma `diag_sub_mem`, the `D_p` preserve `E`. They commute
   (`commute_diagDiff`, from the Library lemma `commute_ee`). On the circle
   `t ↦ exp(t i E_pp)` in `U(n)` (`circle`), which returns to `1` at `t = 2π`
   (`circle_two_pi`), the derivative of `t ↦ μ(ρ(exp(t i E_pp)) w)` is
   `i μ(ρ(exp(t i E_pp)) D_p w)` for every linear functional `μ` (`hasDerivAt_circle`, from the
   Library lemma `hasDerivAt_skewExp` and `π(1 ⊗ i E_pp) = i D_p`). Hence:
   - if `D_p u = c u`, then `μ(ρ(exp(t i E_pp)) u) = exp(i c t) μ(u)` (`apply_circle_of_eigen`).
     Evaluating at `t = 2π` with `μ(u) ≠ 0` gives `exp(2π i c) = 1`, so `c ∈ ℤ` (`eigen_int`);
   - if `D_p u = c u` and `D_p w = c w + u`, then
     `F(t) = exp(-i c t) μ(ρ(exp(t i E_pp)) w) - i t μ(u)` has derivative `0`, so `F(2π) = F(0)`,
     which forces `2π i μ(u) = 0`. Since `μ` is arbitrary, `u = 0`: `D_p` has no Jordan blocks
     (`eq_zero_of_jordan`).

   Restricted to the finite-dimensional space `E`, the commuting family `D_p` makes `E` the sum
   of its joint maximal generalized eigenspaces (Mathlib's
   `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`).
   Since there are no Jordan blocks, `(D_p - c)^(k+1) x = 0` implies `(D_p - c) x = 0`, so these
   generalized eigenspaces are joint eigenspaces. By integrality, each nonzero vector in one of
   them has integer eigenvalues. Induction over the supremum (`Submodule.iSup_induction`) then
   puts `E` inside the span of the integer joint eigenvectors in `E`.

3. **`E` generates `V` under `ℓ`** (`left_generates`). Let `S ⊇ E` be stable under `ℓ`, and let
   `G` be the smallest `ℓ`-stable subspace containing `E` (an `sInf`), so `G ≤ S`. Then:
   - `G` is `r`-stable. The subspace of `s ∈ G` with `r(Z)s ∈ G` for every `Z` contains `E`,
     because `r(Z)e = ℓ(Zᵀ)e - (ℓ(Zᵀ)e - r(Z)e)` and the bracket is in `E` by step 1. It is
     `ℓ`-stable because `ℓ` and `r` commute. Minimality of `G` gives the claim.
   - `G` is `ρ`-stable. `ρ(k)ℓ(Y) = ℓ(kYk*)ρ(k)` (`rho_leftAct`, from the Library lemma
     `rho_mul_pi`), so `G.comap (ρ k)` is `ℓ`-stable and contains `E`.
   - `G` is `π`-stable, since `π(x) = ℓ(x₀) + r(x₁)`.

   `G` contains `E ≠ ⊥`, so irreducibility gives `G = ⊤`, and hence `S = ⊤`.

4. **`ℓ` has an infinitesimal character** (`leftAct_hasInfinitesimalCharacter`). `envFactor` is
   the algebra map `U(𝔤𝔩_n(ℂ)) → U(𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ))` induced by the first factor. The
   enveloping action of `ℓ` is that of `π̃` composed with `envFactor`
   (`envelopingAction_leftAct`). `envFactor` maps the center into the center
   (`envFactor_mem_center`). The second factor commutes with its image (`commute_envFactor`),
   and the first factor commutes with the image of a central element. Both are proved by
   the Library induction principle `InfinitesimalCharacter.envInduction`. The Library lemma
   `prodAction_hasInfinitesimalCharacter` says that `π̃` has an infinitesimal character, so a
   central `z` acts through `ℓ` as the scalar by which `envFactor z` acts through `π̃`.

Applying the bimodule statement to `ℓ`, `r`, `E` and these four facts gives
`span {ℓ(E_pq) v | p < q} ≠ ⊤`. Since `ℓ(E_pq) = ee π 0 p q` by definition, this is the
conclusion of `ComplexJacquetOneSidedStatement`.

## Use

With the Library's `complexJacquetBimoduleReduction` and `complexJacquetModuleFinite_of_oneSided`,
this reduces `ComplexJacquetModuleFiniteStatement` to `BernsteinGelfandInputsStatement`.
