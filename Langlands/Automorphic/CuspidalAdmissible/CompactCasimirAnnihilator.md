# A uniform polynomial annihilating the compact Casimir on a multiplicity space

Module: `Langlands.Automorphic.CuspidalAdmissible.CompactCasimirAnnihilator`.
Provenance: internal. Second algebraic step of the proof of joint admissibility of unitary
cuspidal realizations: for a fixed finite-dimensional representation `σ` of the standard
compact group, the compact Casimir `Ω_K = ∑ Y_j²` acts on the images of all
`σ`-equivariant maps through one fixed nonzero polynomial. Classically this is because
`Ω_K` acts on each `K`-isotypic component by finitely many scalars; the Lean route avoids
`K`-types and uses only differentiation against linear functionals.

All declarations are in `Langlands.Automorphic.CuspidalAdmissible`.

## Generic part

Let `V` be a complex vector space, `ρ` a representation of the standard compact group
`standardInfiniteCompact F n` on `V`, and `A : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ End V` a complex
Lie action with `CompactDualDerivative ρ A` (the Library's notion: along every compact
curve `c` through `1` with real tangent `X`, `t ↦ μ (ρ (c t) v)` has derivative
`μ (A (complexify X) v)` at `0` for every linear functional `μ`).

- `IsPiStable T W` (for `W ⊆ ι → V`): `W` is stable under the componentwise action of `T`;
  closed under products, sums and finite sums (`IsPiStable.mul`, `.add`, `.zero`, `.sum`).
  `piEnd ι T` is the componentwise operator.
- `isPiStable_compact`: for finite `ι`, a subspace `W ⊆ ι → V` stable under every
  componentwise `ρ k` is stable under every componentwise `A (complexify Y)`, `Y` in the
  compact Lie subalgebra. Proof: by `Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`
  it suffices that every `μ` vanishing on `W` vanishes on `(A Y w_i)_i`. Split
  `μ = ∑_i μ ∘ single i`; along the compact curve of `Y` (`compactTangentCurve`) the function
  `t ↦ μ ((ρ (c t) w_i)_i)` is identically `0` and has derivative
  `μ ((A Y w_i)_i)` (`HasDerivAt.fun_sum` of the dual derivatives); uniqueness of
  derivatives gives `0`.
- `compactSquareOperator A := ∑_j A (complexify Y_j)²` over the normalized compact Cartan
  basis `compactCartanBasis F n`; `isPiStable_compactSquareOperator`: it preserves the same
  subspaces.
- `exists_annihilator_of_piStable T hT σ` (**uniform annihilator**): if `T` preserves
  every `ρ`-componentwise-stable `W ⊆ ι → V` (finite `ι` in the universe of `V`), then
  for every representation `σ` on `Fin m → ℂ` there is `p ≠ 0` with `p(T) (φ v) = 0` for
  every `σ`-to-`ρ` equivariant `φ` and every `v`. Proof:
  1. Among the common kernels `⋂_{φ ∈ s} ker φ` of finite sets `s` of equivariant maps, take
     a minimal one `N₀ = ⋂_{φ ∈ s₀} ker φ` (`wellFounded_lt` on subspaces of `Fin m → ℂ`).
     By minimality `N₀ ⊆ ker φ` for every equivariant `φ`.
  2. The range `R₀` of `v ↦ (ψ v)_{ψ ∈ s₀}` is componentwise `ρ`-stable (equivariance), hence
     `T`-stable; it is finite-dimensional. Let `p` be the characteristic polynomial of `T`
     on `R₀` (monic, nonzero).
  3. For any equivariant `φ`, the range `R₁` of `v ↦ (φ v, (ψ v)_{ψ ∈ s₀})` (index
     `Option s₀`) is also `T`-stable, so `p(T)` of `(φ v, (ψ v)_ψ)` equals
     `(φ v', (ψ v')_ψ)` for some `v'`. Forgetting the first coordinate intertwines the
     componentwise `T` (`aeval_intertwine`), so `(ψ v')_ψ = p(T)|_{R₀} (ψ v)_ψ = 0`,
     i.e. `v' ∈ N₀ ⊆ ker φ`. Reading the first coordinate, `p(T) (φ v) = φ v' = 0`.

## The realization

For `S : OperatorRealization F n`:

- `compactCasimirOperator S := S.envelopingAction (compactCartanSquareSum F n)`.
- `envelopingAction_realEnvelopingGenerator`: `S.envelopingAction` of a real enveloping
  generator is `S.complexLieAction (complexify Y)` (definitional).
- `compactCasimirOperator_eq`: `compactCasimirOperator S = compactSquareOperator
  S.complexLieAction` (`map_sum`, `map_mul`).
- `exists_compactCasimir_annihilator S σ`: for every representation `σ` of the standard
  compact group on `Fin m → ℂ` there is `p ≠ 0` with `p(Ω_K) (φ v) = 0` for every
  `φ : (Fin m → ℂ) →ₗ S.Space` with `φ (σ k v) = S.compactRepresentation k (φ v)` and every
  `v`. It applies the generic theorem with `ρ = S.compactRepresentation`,
  `A = S.complexLieAction` and the Library's `S.compactDualDerivative`.
