# The unitary representation of a cone element over the left ideal

Module `Langlands.Representation.Unitary.TemperedComponentGNS` takes the algebra
`𝒜 = algebra μ π hπ` of `Langlands.Representation.Unitary.TemperedComponentAlgebra` (for a unitary,
jointly continuous `π`) and a cone element `F` over `𝒜`
(`Langlands.Analysis.KernelCone.IsConeElement`), and builds a unitary representation of `G`.

## The space `VL hF`

`kernelL hF` is the kernel of `F` restricted to the indices `(x, k, w)` with `x ∈ leftIdeal μ π hπ`
(through `inclL`); `VL hF` is its Hilbert space, with vectors `vecL' hF x k w`. The index inclusion
gives a linear isometry `iotaL hF : VL hF → Space hF` with `iotaL (vecL' x k w) = vec x k w`
(`iotaL_vec`). The vector `vecL' x k w` is linear in `x` and in `w`, and
`‖vecL' x k w‖ ≤ ‖x‖ ‖vec 1 k w‖` (`norm_vecL'_le`), so `x ↦ vecL' x k w` is a bounded linear map
`lambdaL hF k w` on the closed subspace `leftIdeal`.

## The representation `σ`

`sigma hF hπu : G →* (VL hF →L[ℂ] VL hF)` is induced by the index map `x ↦ π(g) x`, which preserves
the kernel because `π(g)^* π(g) = 1`; so each `σ(g)` is a linear isometry with inverse `σ(g⁻¹)`
(`sigma_mem_unitary`). On spanning vectors, `σ(g) (vecL' x k w) = vecL' (π(g) x) k w` (`sigma_vec`),
which is continuous in `g` by `continuous_rep_mul`. A representation by contractions that is
strongly continuous on a set with dense span is jointly continuous
(`isContinuousRepresentation_of_dense`), so `σ` is jointly continuous
(`isContinuousRepresentation_sigma`).

## Left multiplication and integrated operators

`rhoL hF hπu c` (`c ∈ 𝒜`) is left multiplication on the left-ideal indices (`leftIdeal` is a left
ideal of `𝒜`), bounded by `‖c‖`, with `iotaL ∘ rhoL c = rho c ∘ iotaL` (`iotaL_rhoL`); it is a
unital `*`-representation (`adjoint_rhoL`, `rhoL_mul`, `rhoL_add`, `rhoL_smul`, `rhoL_one`) and
continuous in `c` (`rhoLLin`, `continuous_rhoL`). The integrated operators of `σ` are left
multiplications: `σ(φ) (vecL' x k w) = vecL' (π(φ) x) k w` (`testOp_sigma_vec`), hence
`σ(φ) = rhoL (π(φ))` (`testOp_sigma_eq_rhoL`). The proof applies the bounded map `lambdaL` to the
Bochner integral `π(φ) x = ∫ φ(g) • π(g) x` in `leftIdeal`.

## Irreducibility

Let `M` be a closed `σ(G)`-invariant subspace and `P` its orthogonal projection. Then `P`
commutes with `σ(G)` (`starProjection_sigma`), hence with every `σ(φ)` and `σ(φ)^*`, hence with
`rhoL c` for all `c ∈ 𝒜` (`commute_starProjection_rhoL`: the set of such `c` is a closed
`*`-subalgebra containing the generators `π(φ)`). The conjugate `conjProj hF M = ι P ι^*` on
`Space hF` is a star projection (`isStarProjection_conj`, using `ι^* ι = 1`) commuting with
`rho` (`commute_conjProj`). If the weights are strictly positive (`∀ k, 0 < c k`) and `F` is a
nonzero extreme point of `coneSet Rel c e`, `conjProj` is `0` or `1` by `Langlands.Analysis.KernelCone.eq_zero_or_one_of_extreme`, so
`P = ι^* (ι P ι^*) ι` is `0` or `1` and `M` is `⊥` or `⊤`. This is
`isTopologicallyIrreducible_sigma`, under the hypothesis that `VL hF` is nontrivial.

## Provenance

Internal; a GNS-type construction (compare the GNS representation of a function of positive type,
G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., 2015, §3.3, Theorem 3.20)
adapted to the operator-valued kernels.
