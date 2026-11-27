# The derivative of the normalizing factor as a real trace on the radical directions

Module `Langlands.Global.InfiniteAdelicRadicalTangentTrace`, namespace
`Langlands.Global.InfiniteAdelicGroupPoints`. The notation is that of
`InfiniteAdelicTangentKernel` and `InfiniteAdelicRadicalDerivative`. For an affine group `G`
with `hsmooth`, `𝔤_ℝ = GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)` is
the real Lie algebra of `G(F_∞)` with Mathlib's bracket, for the Library's Lie group structure
`smoothLieGroup F G hsmooth`. For a morphism `j`, `pointTangent F hsmoothH hsmooth j` is the
tangent map at the identity of `j` on archimedean points (module
`InfiniteAdelicLeviEnveloping`).

## Declarations

- `tangentKernelInv`: the inverse of the bijection `tangentKernel F hsmooth`
  (`tangentKernel_bijective`). `tangentKernel_tangentKernelInv` and
  `tangentKernelInv_tangentKernel` are the two inverse laws. `tangentKernelInv_add` and
  `tangentKernelInv_smul` (`tangentKernelInv (realAdele F r • x) = r • tangentKernelInv x`)
  follow from `tangentKernel_add` and `tangentKernel_smul`.
- `radicalTangent F hsmooth w = tangentKernelInv (Lie (iV ≫ q) w)`, for `w` in
  `Lie V ⊗ F_∞` and morphisms `iV : V ⟶ Q`, `q : Q ⟶ G`. `tangentKernel_radicalTangent`,
  `radicalTangent_add` and `radicalTangent_smul` say it is additive and real-linear (real
  numbers acting on `Lie V ⊗ F_∞` through `realAdele`). `radicalTangent_injective` says it is
  injective when `iV` and `q` are monomorphisms.
- `radicalTangent_mem` and `exists_radicalTangent_eq`: for a real subspace `V_ℝ ⊆ 𝔤_ℝ` with
  `X ∈ V_ℝ ↔ tangentKernel X ∈ range (Lie (iV ≫ q))` (hypothesis `hVR`), `radicalTangent` maps
  onto `V_ℝ`.
- `radicalTangent_normalAdjoint`: for `c : H ⟶ M`, `l : M ⟶ Q`, `V` normal in `Q` and `Y` an
  identity tangent vector of `H(F_∞)`,

  ```text
  radicalTangent (normalAdjoint (Lie l (Lie c (B Y))) w) = ⁅dι Y, radicalTangent w⁆,
  ι = c ≫ l ≫ q.
  ```

  Both sides are compared after `tangentKernel`. The right side becomes
  `⁅Lie ι (B Y), Lie (iV ≫ q) w⁆` by `tangentKernel_lie` and `tangentKernel_pointTangent`
  (module `InfiniteAdelicTangentKernelNaturality`). The
  left side becomes `Lie q ⁅Lie l (Lie c (B Y)), Lie iV w⁆` by `targetMapLinear_normalAdjoint`.
  They agree because Lie maps preserve brackets (`Lie.targetMapLinear_lie`) and compose
  (`targetMapLinear_comp_apply`).
- `pointTangent_lie_mem`: under `hVR`, `ad (dι Y)` maps `V_ℝ` into itself.
- `identityDerivative_halfModulus_eq_radicalTrace`: let `G` be connected reductive, `q : Q ⟶ G`
  a parabolic subgroup with geometric unipotent radical `iV` and rational Levi subgroup `l`, and
  let `c : H ⟶ M` and `V_ℝ` satisfy `hVR`. Then

  ```text
  identityDerivative (m ↦ δ_Q(c(m))^{-1/2}) Y = -1/2 · tr_ℝ (ad (dι Y) | V_ℝ),
  ι = c ≫ l ≫ q,
  ```

  where `identityDerivative` (module `InfiniteAdelicLeviEnveloping`) is the real derivative at
  the identity. Proof:
  - `mfderiv_halfModulus_one_eq_radicalTrace` gives
    `-1/2 · Σ_v mult(v) · Re (tr_{F_∞} normalAdjoint …)_v`.
  - Give `Lie V ⊗ F_∞` the real structure through `realAlgebra F`. Then
    `trace_restrictScalars_eq_sum` (module `InfiniteAdelicRealTrace`) turns the sum into the
    real trace of `normalAdjoint …`. The Lie algebra is finite free over `F_∞` by
    `Lie.free_finite_lieKernel`.
  - `radicalTangent` is a real-linear isomorphism of `Lie V ⊗ F_∞` onto `V_ℝ`. By
    `radicalTangent_normalAdjoint` it conjugates `normalAdjoint …` to `ad (dι Y)` restricted to
    `V_ℝ`, and `LinearMap.trace_conj'` gives the equality of traces.

## Provenance

Internal. For `ι = l ≫ q` (`c = 𝟙`) and `V_ℝ` the real Lie algebra of `V(F_∞)` inside
`𝔤_ℝ`, the theorem says that the derivative of `δ_Q^{-1/2}` at the identity is `-ρ_Q`, where
`ρ_Q = 1/2 · tr(ad | Lie V(F_∞))` is, on a Cartan subalgebra, half the sum with
multiplicity of the roots occurring in `Lie V`. This is the shift by
`-ρ` in the normalized Harish-Chandra projection (Knapp–Vogan, Chapter IV §8, (4.124)). The
module does not identify `V_ℝ`: it takes `hVR` as a hypothesis.
