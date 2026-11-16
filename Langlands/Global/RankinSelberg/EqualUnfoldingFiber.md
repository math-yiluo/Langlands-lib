# The fiber computation in the equal-rank unfolding

This is an internal helper module for `EqualUnfoldingReduction.md`. Provenance: internal. It
proves, for abstract groups, the measure-theoretic identity behind the step in Cogdell,
*Analytic theory of L-functions for GL_n* (2004), §2.3, printed p.210, where the integral over
`Z_n(𝔸) P'_n(F) \ GL_n(𝔸)` of the integrand containing the section `F(g, Φ; s, χ)` (an integral
over `𝔸^×`) becomes the integral over `P_n(F) \ GL_n(𝔸)`. Cogdell takes this for granted. The
Library's central quotient measure is a restriction of Haar measure to a slab, so the identity
needs a counting argument. Namespace: `Langlands.Global.RankinSelbergGlobal.EqualUnfolding`.

## Setting

`H` and `Z` are groups with measurable multiplication and inversion. `μ` on `H` and `ν` on `Z`
are left-invariant s-finite measures. `σ : Z →* H` is a measurable homomorphism with central
image (`hσc`). `Γ₁ ≤ Z` and `P ≤ H` are countable subgroups with fundamental domains `D₁`
(for `ν`) and `DP` (for `μ`). `A` and `S` are measurable subsets of `H` such that:

- `hcount`: for every `w ∈ H`,
  `Σ_{b ∈ Γ₁} Σ_{p ∈ P} 1_A(σ(b) p⁻¹ w) = 1_S(w)`. In words, the translates `σ(b) p⁻¹ w` meet `A`
  exactly once when `w ∈ S` and never otherwise;
- `hfiber`: for every `x ∈ H`, `ν(D₁ ∩ {z | σ(z)⁻¹ x ∈ S}) = 1`.

In the application (`EqualUnfoldingCount.md`), `H = GL_n(𝔸)`, `Z = GL_1(𝔸)` with
`ideleMeasure`, `σ = scalarPoint`, `Γ₁ = GL_1(F)`, `P = P_n(F)`, `A = D' ∩ S` and `S` is the
slab `1 ≤ |det| < e^n`.

## Results

- `lintegral_fiber`: for measurable `h : H → [0, ∞]` that is left `P`-invariant,
  `∫⁻_{x ∈ A} ∫⁻_z h(σ(z) x) dν dμ = ∫⁻_{x ∈ DP} h dμ`. Proof: (1) translate the inner integral
  by `σ(z)` (left invariance of `μ`). (2) Exchange the integrals twice
  (`lintegral_lintegral_swap`), so that the left side becomes `∫⁻ h · c dμ` with
  `c(y) = ∫⁻_z 1_A(σ(z)⁻¹ y) dν`. (3) Show `Σ_{p ∈ P} c(p⁻¹ x) = 1`: fold the `z`-integral
  over `Γ₁` with `D₁`, apply `hcount` (with centrality of `σ`) and then `hfiber`. (4) Fold the
  `μ`-integral over `P` with `DP` (`IsFundamentalDomain.lintegral_eq_tsum'`) and use the
  `P`-invariance of `h`.
- `map_fiber`: the same identity as an equality of measures on `P \ H`. The image of
  `(μ|_A) × ν` under `(x, z) ↦ P σ(z) x` is the image of `μ|_DP` under the projection. The proof
  applies `lintegral_fiber` to indicators of preimages.
- `integrable_and_integral_fiber`: for measurable left `P`-invariant `K : H → ℂ` integrable on
  `DP`, the function `(x, z) ↦ K(σ(z) x)` is integrable for `(μ|_A) × ν` and has the same
  integral as `K` on `DP`. Proof: `K` descends to `P \ H` (`LeftCosetSpace.lift`), and both
  claims transfer through `map_fiber` (`integrable_map_measure`, `integral_map`).
