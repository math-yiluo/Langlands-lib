# The weight-window locus: base change, field descent and openness

Author: Worker 1421.

This is an internal module for the chart construction of task
`45ac6e52-a4d8-4414-91f1-03c3be35223e`. It continues Worker 1421's
`HopfPointWeightWindow` and uses its notation. `A` is an `R`-bialgebra, `V` an
`R`-module with coaction `δ : V → V ⊗ A`, and `β : A →ₐ[R] C[M]` an algebra
map. `proj δ β l` is the weight-`l` projector on `C ⊗ V`, and
`WeightsIn δ β T` says that every projector for a weight `l ∉ T` vanishes.
Geometrically, these lemmas say that the locus where the weights of the
comodule `V` lie in `T` is stable under base change, descends from field
extensions, and is open.

## Results

- `proj_mapAlgHom_tmul`: for `ψ : C →ₐ[R] D`, the projector of
  `mapAlgHom ψ ∘ β` sends `d ⊗ v` to `d • (ψ ⊗ id) (proj δ β l (1 ⊗ v))`. This
  follows from `HopfPointWeightWindow.rTensor_proj`.
- `weightsIn_mapAlgHom`: weight windows are preserved by every change of
  coefficients `ψ`. The proof is by induction on tensors, using the previous
  lemma.
- `weightsIn_of_mapAlgHom`: weight windows descend along a change of
  coefficients `ψ` for which `ψ ⊗ id_V` is injective. Again this uses
  `rTensor_proj`.
- `rTensor_injective_of_field`: for a homomorphism `ψ : K →ₐ[R] L` from a field
  to a nonzero ring, `ψ ⊗ id_V` is injective. `L` is faithfully flat over `K`,
  so `K ⊗ V → L ⊗_K (K ⊗ V)` is injective (Mathlib's
  `Module.FaithfullyFlat.tensorProduct_mk_injective`). Then cancel the base
  change (`AlgebraTensorModule.cancelBaseChange`).
- `rTensor_smul`: `(ψ ⊗ id)(g • y) = ψ g • (ψ ⊗ id) y`.
- `exists_away_weightsIn` (needs `V` finite, `IsCoassoc δ` and `IsHopfPoint β`):
  suppose the weights of the residue-field point at a prime `p` lie in `T`.
  Then for some `f ∉ p` the weights of the point over `C_f` lie in `T`.
  Proof: only the finitely many weights in some finite `T₀` have nonzero
  projectors (`exists_finite_weightsIn`). For each such `l ∉ T`, the projector
  is idempotent (`proj_proj`) and vanishes after tensoring with `κ(p)`. So
  `exists_smul_eq_zero_of_idempotent` gives `g_l ∉ p` with `g_l • proj = 0`.
  Let `f` be the product of the `g_l`. It lies outside `p` because `p` is
  prime. Over `C_f` every `g_l` is a unit, so the corresponding projectors
  vanish. The projectors for `l ∉ T₀` already vanish over `C`, and hence over
  `C_f`.
