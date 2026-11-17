# The `U(n)`-fixed vector of a tempered spherical principal series is cyclic

Module: `Langlands.Representation.Archimedean.SphericalCyclic`, namespace
`Langlands.Archimedean.SphericalCyclic`. Everything here is proved; nothing is assumed.

Notation. `ds` is a list of `n` complex characters (`ds.length = n`).
`X = X(ds) = kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` is the space of
`U(n)`-finite vectors of the standard module. `ρ = complexStandardRep n ds` is the `U(n)`-action,
`π = complexStandardLie n ds` the action of `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`, and `ev₁ = kFiniteEval _ 1` is
evaluation at `1`. `ℓ = leftAct π` and `r = rightAct π` are the two commuting actions of
`𝔤𝔩_n(ℂ)` (module `ComplexJacquetBimoduleBridge`). For skew-Hermitian `Y`,
`π(1 ⊗ Y) = ℓ(Y) - r(Yᵀ)` (`pi_skew_eq`). `U = U(𝔤𝔩_n(ℂ))` (`glU n`), `Λ_ℓ = envelopingAction ℓ`.

"Spherical tempered" means here: every character in `ds` has weight `0`, and all exponents have
the same real part.

## Main results

- `ComplexSphericalTemperedStatement` (a `Prop`) says: for spherical tempered `ds` and every
  nonzero `U(n)`-fixed `T ∈ X`,
  1. every subspace `W ⊆ X` that is stable under `ρ` and `π` and contains `T` is all of `X`;
  2. `X` is irreducible (`IsIrreducibleGKModule ρ π`).
- `complexSphericalTempered : ComplexSphericalTemperedStatement` proves it.
- `irreducible hn hw htemp : IsIrreducibleGKModule ρ π` is the same irreducibility without a given
  `T`; the fixed vector comes from `ComplexSphericalLieGroup.exists_spherical`.

The cyclicity part (1) holds for `W` stable under `π` alone (`fixed_cyclic`); `ρ`-stability is not
used.

Provenance. These are internal steps of the project's proof of
`ComplexTemperedStandardIrreducibleStatement`; the exact formulation is ours. The mathematics is
classical: a unitary spherical principal series is irreducible and its spherical vector is
cyclic. N. Wallach, *Cyclic vectors and irreducibility for principal series representations*,
Trans. Amer. Math. Soc. 158 (1971), 107–113, proves this for complex semisimple groups
(introduction, printed p. 107; Theorems 3.2 and 3.3, printed p. 111), using a theorem of Kostant.
Here the group is the reductive group `GL_n(ℂ)` and the proof is different: it is the
minimal-`K`-type argument of M. Duflo, *Représentations irréductibles des groupes semi-simples
complexes*, Lecture Notes in Math. 497 (1975), 26–88, section IV.1, with Kostant's multiplicity
bound (Library `lowerVermaKostant`) and the kernel theorem of module `SphericalKernel`.

## Fixed vectors (section `Generic`)

These hold for any `(𝔤𝔩_n(ℂ), U(n))`-module `(V, ρ, π)` satisfying `IsComplexGKModule n ρ π`.

- `pi_eq_zero_of_fixed`: a `U(n)`-fixed `v` is killed by `π(1 ⊗ Y)` for skew-Hermitian `Y`. Proof:
  the derivative at `0` of `t ↦ μ(ρ(exp tY) v) = μ(v)` is `0` for every functional `μ`
  (`hasDerivAt_skewExp`).
- `left_eq_right_of_fixed`: a `U(n)`-fixed `v` satisfies `ℓ(Y) v = r(Yᵀ) v` for every `Y`. Proof:
  write `Y = A + iB` with `A = (Y - Y*)/2`, `B = -i(Y + Y*)/2` skew-Hermitian, and use
  `pi_eq_zero_of_fixed` for `A` and `B`.
- `exists_ne_zero_forall_mem_eq_zero`: let `B : ℂ^{d+1} → (W →ₗ ℂ)` be a linear map into the
  functionals on a finite-dimensional `W`, and `W₀ ⊆ W` a subspace of dimension `d`. Then there is
  a nonzero coefficient vector `c ∈ ℂ^{d+1}` such that `B c` vanishes on `W₀`. The functional
  `B c` itself may be zero (for instance when `B = 0`); only `c ≠ 0` is claimed. Proof: the map
  `c ↦ (B c (b_j))_j` into `ℂ^d` (`b` a basis of `W₀`) has a nonzero kernel vector.

## The module `X(ds)` (section `Concrete`)

- `leftAct_center`: every central `z ∈ U` acts on `X` through `ℓ` by a scalar. It comes from the
  infinitesimal character of `X` (`complexStandardLie_hasInfinitesimalCharacter`), transported
  along `tensorLieEquiv` (`Kostant.hasInfinitesimalCharacter_comp`), and from
  `envFactor_mem_center`.
- `mu ds hn p = (κ_p(1) - i κ_p(i)) / 2`, with `κ_p = ComplexSwapJacquet.kappa ds hn p`.
  `mu_eq`: if all weights are `0`, then `μ_p = t_p + (n-1)/2 - p`, where `t_p` is the exponent of
  the `p`-th character. `mu_re`: if moreover all `Re t_p` are equal, then `Re μ_p + p` does not
  depend on `p`.
- `evalJ`: `ev₁` is a Jacquet functional
  (`ComplexTemperedComplement.isComplexJacquetFunctional_eval_comp` with the identity map).
  Consequences, via `eval_leftAct` (`ev₁ ∘ ℓ(Y) = ½ (ev₁ ∘ π(1⊗Y) - i ev₁ ∘ π(1⊗iY))`):
  - `eval_leftAct_upper`: `ev₁(ℓ(E_pq) v) = 0` for `p < q`;
  - `eval_leftAct_diag`: `ev₁(ℓ(E_pp) v) = μ_p ev₁(v)`;
  - `eval_kappa_diag`: if all weights are `0`, then `ev₁(ℓ(E_pp) v - r(E_pp) v) = 0`.
- `eq_smul_of_fixed`: if `T` is `U(n)`-fixed with `ev₁ T = 1`, every `U(n)`-fixed `v` equals
  `ev₁(v) T`. `eval_ne_zero_of_fixed`: a nonzero fixed vector does not vanish at `1`. Both use
  `ComplexPermutation.kFiniteEval_one_separating` (a vector is `0` if `ev₁ ∘ ρ(k)` kills it for
  every `k`).

## The orbit map is onto (`orbit_surjective`)

Let `ds` be spherical tempered, `T` `U(n)`-fixed with `ev₁ T = 1`, and `x ∈ X`. Then
`x = Λ_ℓ(u) T` for some `u ∈ U`.

Proof.

1. `ℓ(Y) T = r(Yᵀ) T` (`left_eq_right_of_fixed`). Central elements act on `T` through
   `Λ_ℓ ∘ trU` by `chiV μ` (`env_trU_center_of_functional` from `SphericalKernel`, with the
   functional `ev₁` and `leftAct_center`).
2. Let `W` be the span of the `U(n)`-orbit of `x`. It is finite-dimensional and `U(n)`-stable.
   `σ(Y) = ℓ(Y) - r(Yᵀ)` restricts to a Lie algebra representation of `𝔤𝔩_n(ℂ)` on `W`. In Lean,
   `σ` is `D.kE` for a `BGChase.BData` record `D` with `E = W`. The generic formula is
   `D.kE(Y) = D.r(Y) - D.ℓ(Yᵀ)`, and the proof takes `D.ℓ := r`, `D.r := ℓ`, so
   `σ(Y) = ℓ(Y) - r(Yᵀ)` on `W` (`hσ`). Stability of `W` is `kappa_mem`. `σ` has integral weights,
   by `BData.intSpan_kE` and `le_span_joint`.
3. Kostant (`VermaKostant.lowerVermaKostant` with `χ = chiV μ ∘ trC`) gives `d = dim W₀` linear
   maps `f_i : W → U`, where `W₀ = zeroWeightSpace σ`. They satisfy
   `f_i(σ(Y) w) = ι(Y) f_i(w) - f_i(w) ι(Y)`, and they are linearly independent modulo the left
   ideal `kerSpan χ`.
4. Put `ψ_i(w) = Λ_ℓ(f_i(w)) T`. Then `ψ_i(σ(Y) w) = ℓ(Y) ψ_i(w) - r(Yᵀ) ψ_i(w)`, by step 1 and
   because `Λ_ℓ(a)` commutes with `r(Y)`. In particular `ψ_i(σ(Y) w) = π(1 ⊗ Y) ψ_i(w)` for
   skew-Hermitian `Y`. So `ψ_i` is `U(n)`-equivariant, by
   `ComplexSphericalLieGroup.map_rho_of_map_pi`. The derivative hypothesis needed there for `W`
   comes from the derivative condition of `IsComplexGKModule` for `X`, through an extension of
   functionals from `W` to `X`.
5. The `ψ_i` are linearly independent: if `Σ c_i ψ_i = 0`, then `Λ_ℓ(Σ c_i f_i(w)) T = 0` for every
   `w`. So `Σ c_i f_i(w) ∈ kerSpan χ` (`SphericalKernel.mem_kerSpan`, which uses `mu_re`), and
   `c = 0` by step 3.
6. Consider the `d + 1` maps `ι, ψ_0, …, ψ_{d-1} : W → X` (`ι` the inclusion) and their
   combinations `Ψ_c`, `c ∈ ℂ^{d+1}`. Each `Ψ_c` is `U(n)`-equivariant, and
   `Ψ_c(σ(Y) w) = ℓ(Y) Ψ_c(w) - r(Yᵀ) Ψ_c(w)`. By `exists_ne_zero_forall_mem_eq_zero` there is a
   nonzero `c` with `ev₁ ∘ Ψ_c = 0` on `W₀`.
7. `ev₁ ∘ Ψ_c` also vanishes on `σ(E_pp) W` (`eval_kappa_diag`). `W` is spanned by
   `σ`-weight vectors with integral weights `m`. A weight vector `e` with `m = 0` lies in `W₀`;
   otherwise `e = m_p⁻¹ σ(E_pp) e` for some `p` with `m_p ≠ 0`. So `ev₁ ∘ Ψ_c = 0` on all of `W`.
   Since `Ψ_c` is `U(n)`-equivariant and `W` is `U(n)`-stable, `ev₁(ρ(k) Ψ_c(w)) = 0` for every
   `k`, hence `Ψ_c = 0` (`kFiniteEval_one_separating`).
8. `c_0 ≠ 0`: otherwise `Σ c_{i+1} ψ_i = 0`, so `c = 0` by step 5. Applying `Ψ_c = 0` to `x` gives
   `x = -c_0⁻¹ Σ c_{i+1} ψ_i(x) = Λ_ℓ(u) T` with `u = -c_0⁻¹ Σ c_{i+1} f_i(x)`.

The declaration uses `set_option maxHeartbeats 1000000`.

## Cyclicity and irreducibility

- `env_leftAct_mem`: `Λ_ℓ(u)` preserves every `π`-stable subspace. Induction on `u`
  (`envInduction`); for `u = ι(Y)`, `ℓ(Y)` is a value of `π` (`leftAct_apply`,
  `prodAction_apply`).
- `fixed_cyclic`: if `T ≠ 0` is `U(n)`-fixed, every `π`-stable `W ∋ T` is `⊤`. Apply
  `orbit_surjective` to `(ev₁ T)⁻¹ T`, then `env_leftAct_mem`.
- `irreducible_of_fixed`: `complexTemperedCyclicVector` (module `ComplexTemperedComplement`) with
  the cyclic vector `T`. Its multiplicity hypothesis holds because a `U(n)`-equivariant `E` maps
  `T` to a fixed vector, which is `ev₁(E T) (ev₁ T)⁻¹ T` by `eq_smul_of_fixed`.
- `irreducible`: `irreducible_of_fixed` with the fixed vector of `exists_spherical`.
