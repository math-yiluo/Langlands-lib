# The Dixmier–Malliavin theorem for Lie groups with a closed linear realization

`Langlands.Representation.Archimedean.DixmierMalliavin`. The theorem of Dixmier and Malliavin in the
Library's notions: smooth compactly supported kernels `smoothCompactKernels E G` on a Lie group `G`
modelled on `𝓘(ℝ, E)`, and their convolution `gardingKernelConvolution μ`
(`GardingKernelOperations`). Namespace `Langlands.Archimedean`.

## Statements

- `exists_eq_sum_gardingKernelConvolution`: let `G` be a Lie group (`[ChartedSpace E G]`,
  `[LieGroup 𝓘(ℝ, E) ∞ G]`, Hausdorff, locally compact, with its Borel structure) with a closed linear
  realization `hρ : LinearLieGroup.IsClosedLinearRealization 𝓘(ℝ, E) ρ`, `ρ : G →* 𝔸ˣ` for a
  finite-dimensional normed real algebra `𝔸`; let `μ` be a left Haar measure and `U` a neighbourhood
  of `1`. Then every `f : smoothCompactKernels E G` is
  `f = ∑ i, gardingKernelConvolution μ (φ i) (ψ i)` for some `n` and
  `φ ψ : Fin n → smoothCompactKernels E G` with `tsupport (φ i) ⊆ U` and
  `tsupport (ψ i) ⊆ tsupport f`. Pointwise: `f x = ∑ᵢ ∫ φᵢ(a) ψᵢ(a⁻¹ x) dμ(a)`.
- `exists_eq_sum_gardingKernelConvolution_units`: the same for `G = 𝔸ˣ` with Mathlib's manifold
  structure (`ρ = id`, `LinearLieGroup.isClosedLinearRealization_id`). This covers `GL_n(ℝ)`,
  `GL_n(ℂ)`, `GL_n` over a product of copies of `ℝ` and `ℂ`, and the units of every
  finite-dimensional real algebra.
- `Langlands.Hecke.convolutionIntegral_comp_continuousMulEquiv`: for `e : G ≃ₜ* G'` (Borel on both
  sides), `convolutionIntegral μ (f ∘ e) (g ∘ e) x = convolutionIntegral (μ.map e) f g (e x)`, by the
  change of variables `integral_map_equiv`.

## Proof

Let `K = ρ.range` with its exponential structure and `e = hρ.rangeEquiv : G ≃ₜ* K`
(`Langlands/Geometry/Manifold/LinearLieGroup/Realization`). The image `μ.map e` is a left Haar
measure on `K` (with the Borel structure of `K`). The function `f ∘ e.symm` is smooth for the
exponential charts and compactly supported, and `e (U)` is a neighbourhood of `1`; the theorem on
linear groups, `LinearLieGroup.IsExpLieAlgebra.exists_eq_sum_convolutionIntegral`
(`Langlands/Analysis/DixmierMalliavin/LinearGroup`), writes it as `∑ φ'ᵢ ⋆ ψ'ᵢ` with the support
conditions. Then `φᵢ = φ'ᵢ ∘ e` and `ψᵢ = ψ'ᵢ ∘ e` are smooth (`contMDiff_iff_comp_symm`), compactly
supported, with supports `e⁻¹(tsupport φ'ᵢ) ⊆ U` and `e⁻¹(tsupport ψ'ᵢ) ⊆ tsupport f`, and the
convolutions correspond by `convolutionIntegral_comp_continuousMulEquiv`.

## Literature

J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), §3, Théorème 3.1; page 6 of the English
translation *Factorizations of infinitely differentiable functions and smooth vectors* (translator
not named, with its own page numbers), where it is Theorem 3.1, proved on pages 6–7; the theorem
there is stated for every real Lie group, while the statement here assumes a closed linear
realization (see the page of `Realization`). J. R. Getz and H. Hahn, *An introduction to automorphic
representations* (2024), state the factorization as Theorem 4.2.9, §4.2, p. 110, which the page of
`Langlands/Analysis/BoundedContinuousSmoothingStatement` cites, and use it for a trace-class
argument in the proof of Lemma 9.3.3, p. 248.
