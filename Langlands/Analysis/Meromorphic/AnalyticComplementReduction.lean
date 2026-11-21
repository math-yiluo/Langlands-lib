import Langlands.Analysis.Meromorphic.ContinuationPrincipleReduction
import Langlands.Analysis.Meromorphic.CommonZeroSets

/-! # Analyticity of the non-uniqueness locus, from Hartogs's theorem

Bernstein–Lapid, Theorem 3.3 (1), the analyticity of `M ∖ M_unq`, with Hartogs's theorem in
the diagonal form `HartogsDiagonal E` as the one named premise. Near every point, on a chart
ball `W` carrying a finite-type frame, `M_unq ∩ W` is the set where some `n × n` minor
`det (scalarMatrix μ ℓ a s)` of the scalarized system does not vanish
(`mem_uniqueSolutionLocus_iff_exists_det_ne_zero`). So the complement is locally the common
zero set of the holomorphic family of all these minors (`IsLocallyCommonZeroSet`), hence
analytic (`IsLocallyCommonZeroSet.isAnalyticSubset`, which uses the local finiteness theorem
`exists_finset_zero_iff`). -/

noncomputable section
set_option autoImplicit false

universe uE uM uV uι uF

namespace Langlands.Analysis.Meromorphic

open Set
open scoped Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  {ι : Type uι} {F : ι → Type uF} [∀ i, AddCommGroup (F i)] [∀ i, Module ℂ (F i)]
  [∀ i, Module ℝ (F i)] [∀ i, IsScalarTower ℝ ℂ (F i)] [∀ i, TopologicalSpace (F i)]
  [∀ i, IsTopologicalAddGroup (F i)] [∀ i, ContinuousSMul ℂ (F i)]
  [∀ i, LocallyConvexSpace ℝ (F i)] [∀ i, T2Space (F i)]

omit [FiniteDimensional ℂ E] in
/-- The complement of the unique-solution locus is locally the common zero set of the
holomorphic family of `n × n` minors of the scalarized system (Hartogs's theorem assumed). -/
theorem isLocallyCommonZeroSet_compl_uniqueSolutionLocus [ConnectedSpace M]
    (hH : HartogsDiagonal E) {μ : ∀ i, M → V →L[ℂ] F i} {c : ∀ i, M → F i}
    (hsys : IsAnalyticSystem 𝓘(ℂ, E) μ c)
    (hft : IsLocallyFiniteType 𝓘(ℂ, E) (systemSolutions μ c))
    (hint : (interior (uniqueSolutionLocus μ c)).Nonempty) :
    IsLocallyCommonZeroSet.{max uι uF} (E := E) (uniqueSolutionLocus μ c)ᶜ := by
  intro s₀
  obtain ⟨W, hWb, hs₀W, n, ℓ, hℓ, hinj, hrange⟩ := exists_chartBall_frame hft s₀
  have hWo := hWb.isOpen
  have hmeets : (W ∩ interior (uniqueSolutionLocus μ c)).Nonempty := by
    have hs : s₀ ∈ closure (interior (uniqueSolutionLocus μ c)) := by
      rw [closure_interior_uniqueSolutionLocus_eq_univ hH hsys hft hint]
      exact mem_univ s₀
    exact mem_closure_iff.1 hs W hWo hs₀W
  refine ⟨W, hWo, hs₀W, Fin n → Σ i, (F i →L[ℂ] ℂ),
    fun a s => (scalarMatrix μ ℓ a s).det,
    fun a => mdifferentiableOn_det_scalarMatrix hH hsys hWo hℓ a, ?_⟩
  ext s
  simp only [mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hs, hsW⟩
    refine ⟨hsW, fun a => ?_⟩
    by_contra ha
    exact hs ((mem_uniqueSolutionLocus_iff_exists_det_ne_zero hH hsys hWb hℓ hinj hrange
      hmeets hsW).2 ⟨a, ha⟩)
  · rintro ⟨hsW, hs⟩
    refine ⟨fun hsP => ?_, hsW⟩
    obtain ⟨a, ha⟩ := (mem_uniqueSolutionLocus_iff_exists_det_ne_zero hH hsys hWb hℓ hinj
      hrange hmeets hsW).1 hsP
    exact ha (hs a)

/-- **The non-uniqueness locus is analytic** (Bernstein–Lapid, Theorem 3.3 (1)), assuming
Hartogs's theorem in the form `HartogsDiagonal E`. -/
theorem isAnalyticSubset_compl_uniqueSolutionLocus_of_hartogs [ConnectedSpace M]
    (hH : HartogsDiagonal E) {μ : ∀ i, M → V →L[ℂ] F i} {c : ∀ i, M → F i}
    (hsys : IsAnalyticSystem 𝓘(ℂ, E) μ c)
    (hft : IsLocallyFiniteType 𝓘(ℂ, E) (systemSolutions μ c))
    (hint : (interior (uniqueSolutionLocus μ c)).Nonempty) :
    IsAnalyticSubset 𝓘(ℂ, E) (uniqueSolutionLocus μ c)ᶜ :=
  (isLocallyCommonZeroSet_compl_uniqueSolutionLocus hH hsys hft hint).isAnalyticSubset

end Langlands.Analysis.Meromorphic
