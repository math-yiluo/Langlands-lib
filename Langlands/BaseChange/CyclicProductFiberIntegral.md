# Fibre integrals over the ordered product: Schwartz–Bruhat functions and unit tensors

`Langlands.BaseChange.CyclicProductFiberIntegral`. Namespace `Langlands.BaseChange`.

Generic statements about a topological group `G`; no field appears. The fibre integral
`splitFiberIntegral`, its value `splitFiberIntegral_tensor` on tensors, and the orbital identity in
cyclic product coordinates for arbitrary continuous compactly supported functions on the product
(`cyclicProductOrbitalIntegral_eq_splitFiberIntegral`) are in
`Langlands.BaseChange.CyclicProductConvolution`, which this file imports. This file treats the
fibre integrals of Schwartz–Bruhat functions and of unit tensors.

## Statements

Throughout, `G` is a group with `[TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]`,
`m : ℕ`, `μ : Measure G`, and `splitProductFiberChart m (y, w) = Fin.snoc w ((List.ofFn w).prod⁻¹ * y)`
is the Library's chart of `G^{m+1}` by the total ordered product and the first `m` coordinates.

Here `splitFiberIntegral μ Φ : G → ℂ` for `Φ : (Fin (m + 1) → G) → ℂ` is
`splitFiberIntegral μ Φ y = ∫ w, Φ (splitProductFiberChart m (y, w)) ∂Measure.pi (fun _ : Fin m => μ)`
(module `CyclicProductConvolution`), the integral of `Φ` over the fibre of `x ↦ x₀ ⋯ x_m` above
`y`.

- `splitFiberIntegral_mem_schwartzBruhat [T2Space G] (μ) (Φ : SchwartzBruhat (Fin (m + 1) → G)) :
  splitFiberIntegral μ Φ ∈ schwartzBruhatSubmodule G`. No hypothesis on `μ`.
- `support_splitFiberIntegral_subset (μ) (K₀ : Subgroup G) (Φ)
  (hΦ : Function.support Φ ⊆ Set.pi Set.univ fun _ => (K₀ : Set G)) :
  Function.support (splitFiberIntegral μ Φ) ⊆ K₀`.
- `splitUnitTensor μ K ψ : (Fin (m + 1) → G) → ℂ` for `K : Set G`, `ψ : G → ℂ`:
  `x ↦ (μ K).toReal⁻¹ ^ m * (Set.pi Set.univ fun _ => K).indicator 1 (Fin.init x) * ψ (x (Fin.last m))`,
  the tensor of `m` normalized indicators of `K` with `ψ` in the last coordinate.
- `splitUnitTensor_mem_schwartzBruhat [T2Space G] (μ) (K : Subgroup G) (hKo : IsOpen (K : Set G))
  (hKc : IsCompact (K : Set G)) (ψ : SchwartzBruhat G) :
  splitUnitTensor (m := m) μ K ψ ∈ schwartzBruhatSubmodule (Fin (m + 1) → G)`.
- `splitFiberIntegral_splitUnitTensor (μ) [SigmaFinite μ] (K : Subgroup G)
  (hKm : MeasurableSet (K : Set G)) (hK0 : μ K ≠ 0) (hKt : μ K ≠ ⊤) (ψ : G → ℂ)
  (hψ : ∀ k ∈ K, ∀ x, ψ (k * x) = ψ x) :
  splitFiberIntegral μ (splitUnitTensor (m := m) μ K ψ) = ψ`.

## Proofs

- Schwartz–Bruhat: `K(y, w) = Φ(splitProductFiberChart m (y, w))` is locally constant with compact
  support; with `Y` the (compact) projection of its support to `G^m`, compactness of `Y` gives a
  neighbourhood of `y₀` on which `K(y, w) = K(y₀, w)` for all `w ∈ Y`
  (`IsCompact.eventually_forall_of_forall_eventually`), and both vanish off `Y`; the support lies
  in the compact projection of the support of `K` to `G`.
- Support: if the integrand is nonzero at `w`, all `w_i` and `(w₀ ⋯ w_{m-1})⁻¹ y` lie in `K₀`, so
  `y ∈ K₀`.
- Unit tensor: at `(y, w)` the integrand is `μ(K)^{-m} 1_{K^m}(w) ψ((w₀ ⋯ w_{m-1})⁻¹ y)`, which is
  `μ(K)^{-m} 1_{K^m}(w) ψ(y)` by left invariance; `μ^{⊗m}(K^m) = μ(K)^m`.

## Declarations, in order

`splitFiberIntegral_mem_schwartzBruhat`, private `mem_of_forall_snoc_mem`,
`support_splitFiberIntegral_subset`, `splitUnitTensor`, `splitUnitTensor_mem_schwartzBruhat`,
`splitFiberIntegral_splitUnitTensor`.

## Literature

- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour GLₙ en
  caractéristique non nulle*, Mém. SMF 124 (2011), §I.2.4, pp. 15–16: the change of variables
  `g⁻¹ δ g^σ = (h₁ y h₁^τ h₂⁻¹, h₂ h₃⁻¹, …, h_r)` and the identity
  `Λ_σ^{G(E)}(φ, δ) = Λ_τ^{G(E₁)}(φ*, y)`, `y = δ₁ ⋯ δ_r`, where `φ ↦ φ*` is the linear extension
  of `φ₁ ⊗ ⋯ ⊗ φ_r ↦ φ₁ * ⋯ * φ_r` through `C_c^∞(G(E)) = C_c^∞(G(E₁))^{⊗r}`. The fibre integral
  is this map written as one integral, which avoids the identification with the tensor product;
  `cyclicProductOrbitalIntegral_eq_splitFiberIntegral` of `CyclicProductConvolution` is the
  identity (HL solve the chart for the first coordinate, the Library's `splitProductFiberChart` for
  the last). §I.2.6, p. 18: the
  formula for `φ*` of a tensor, and the function `φ = ψ ⊗ ψ₁ ⊗ ⋯ ⊗ ψ₁` with `ψ₁` the normalized
  characteristic function of a compact open subgroup under which `ψ` is invariant by right
  translations, so that `φ* = ψ`; `splitUnitTensor` puts `ψ` in the last coordinate and asks
  invariance by left translations, as the chart asks.
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), Chapter 1, §5, pp. 48–49: the σ-centralizer in product coordinates (5.1), the
  variables (5.2), and the σ-twisted orbital integral of `φ₁ ⊗ ⋯ ⊗ φ_m` as the τ-twisted orbital
  integral of `φ₁ * ⋯ * φ_m`.
