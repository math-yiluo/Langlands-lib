# Ample higher-cohomology vanishing from the balanced cube identity

This module proves the published
`Langlands.AbelianScheme.AmpleLineBundleHigherCohomologyVanishingStatement`
under one hypothesis: a proof of the balanced cube identity
`Langlands.GroupScheme.FieldCubePullbackStatement`. That statement has no proof
in the Library yet; its proof task is `10d9bd97-8b97-4937-8a1a-3c96c6fb7537`.
So the module is a conditional reduction, not yet the unconditional result.

## Theorem

`Langlands.AbelianScheme.ampleLineBundleHigherCohomologyVanishing_of_cube
  (cube : GroupScheme.FieldCubePullbackStatement.{u}) :
  AmpleLineBundleHigherCohomologyVanishingStatement.{u}`.

The target statement says this. Let `A` be an abelian scheme over an
algebraically closed field `K`, and let `L` be an ample line bundle on `A`.
Then `Hⁱ(A, L) = 0` for every `i > 0`. This is Mumford, Fogarty and Kirwan,
*Geometric Invariant Theory*, 3rd edition, Proposition 6.13 (i); the cited
location is in the statement's own Markdown. The proof below uses that `K`
is algebraically closed in one place: step 6 applies the published
`polarizedFiniteFlatRank`, whose statement
`PolarizedFiniteFlatRankStatement` assumes `[IsAlgClosed K]`. The other
inputs are stated over an arbitrary field.

Two other inputs enter through their published Library proofs:

- `Langlands.AlgebraicGeometry.Modules.properAmplePairSerreVanishing`
  (module `...Modules.ProperAmplePairSerreVanishingProof`). Let `X` be proper
  over a field, `M` quasi-coherent with finite affine sections, and `L₁`,
  `L₂` ample. Then there is one `n₀` with
  `Hⁱ(X, (M ⊗ L₁^a) ⊗ L₂^b) = 0` for all `a, b ≥ n₀` and `i > 0`.
- `Langlands.AlgebraicGeometry.Modules.finiteFlatCohomologyRetract`
  (module `...Modules.FiniteFlatCohomologyRetractProof`). Let
  `f : X → Y` be finite, flat and locally of finite presentation over a
  field, with constant rank `d` that is nonzero in `K`. Then for every
  quasi-coherent `M` on `Y`, `Hⁿ(Y, M)` is a retract of `Hⁿ(X, f^* M)`.

The multiplication formula comes from the companion module
`Langlands.AbelianScheme.FieldMultiplicationPullbackOfCube`.

## Proof as implemented

Write `ψ_k` for multiplication by `k` on `A`.

1. Let `σ = ψ_{-1}` be inversion. It is an involution
   (`multiplicationNegOneIso`), so it is an isomorphism, and `L' = σ^* L` is
   ample (`closedImmersionPullbackAmple`). Then `N = L ⊗ L'` is ample
   (`ampleTensor`) and symmetric:
   `σ^* N ≅ σ^* L ⊗ σ^* σ^* L ≅ L' ⊗ L ≅ N` (`pullbackTensorIso`,
   `pullbackComp`, `pullbackCongr`, `pullbackId`, `tensorComm`).
2. `A` is smooth over `Spec K` and connected, because `Spec K` is a point and
   `A` is geometrically connected. So it has a relative dimension `g`
   (`smoothConnectedRelativeDimension`).
3. Apply `properAmplePairSerreVanishing` with `M = 𝒪_A`, `L₁ = L` and
   `L₂ = L'` to get `n₀`. The structure sheaf is quasi-coherent and has
   finite affine sections.
4. Choose `k ≥ n₀ + 2` with `(k : K) ≠ 0` (`exists_ge_cast_ne_zero`: one of
   `n₀ + 2` and `n₀ + 3` works). Then `C(k+1,2) ≥ n₀` and `C(k,2) ≥ n₀`
   (`le_choose_two`).
5. `fieldMultiplicationPullbackIsoOfCube cube` gives
   `ψ_k^* L ≅ L^{C(k+1,2)} ⊗ L'^{C(k,2)}`. With the left unitor
   `𝒪 ⊗ L^a ≅ L^a`, step 3 gives `Hⁱ(A, ψ_k^* L) = 0` for `i > 0`.
6. `ψ_k` is finite (`multiplication_isFinite_of_ne_zero`) and étale
   (`multiplication_etale_of_field`), so it is flat and locally of finite
   presentation. Its rank is `(k·k)^g` at every point
   (`polarizedFiniteFlatRank`). This uses `N` and the published
   `fieldSymmetricMultiplicationPullbackOfCube cube`, which gives
   `ψ_k^* N ≅ N^{k·k}`. The rank is nonzero in `K` because `k` is.
7. By `finiteFlatCohomologyRetract`, `Hⁱ(A, L)` is a retract of
   `Hⁱ(A, ψ_k^* L) = 0`. Its identity factors through zero, so
   `Hⁱ(A, L) = 0`.

The private lemmas `exists_ge_cast_ne_zero` and `le_choose_two` are the
arithmetic facts used in step 4.

## Authors

Worker 1137 wrote the first version of this argument with the three inputs as
hypotheses. Worker 1147 adapted it to the published statements and then to
the published Serre-vanishing and retraction proofs.
