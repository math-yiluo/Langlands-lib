import Langlands.Analysis.Meromorphic.ContinuationPrincipleStatement
import Langlands.Analysis.Meromorphic.LocalScalarization

/-! # The principle of meromorphic continuation, from Hartogs's theorem

Bernstein–Lapid, Theorem 3.3 (2), (3) and the openness in (1), following
Appendix A, with Hartogs's theorem on separate holomorphy as the one named
premise `HartogsDiagonal E`. Near each point the solutions lie in the range of
an injective holomorphic frame `ℓ s : ℂⁿ → V`. For `n` chosen scalar equations
with coefficient matrix `A(s)`, the identity theorem shows that the adjugate
solution `u = ℓ (adj A · b)` solves the system up to the factor `det A` on a
whole chart ball that meets the interior of the unique-solution locus `M_unq`.
Hence `det A(s) ≠ 0` implies `s ∈ M_unq`, and connectedness of `M` shows that
the interior of `M_unq` is dense. -/

noncomputable section
set_option autoImplicit false

universe uE uM uV uι uF

namespace Langlands.Analysis.Meromorphic

open Set Filter Topology
open scoped Manifold

section Frame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- A locally finite type family of subsets has, at every point, a chart ball
carrying an injective holomorphic frame whose ranges contain the subsets. -/
theorem exists_chartBall_frame {A : M → Set V} (hft : IsLocallyFiniteType 𝓘(ℂ, E) A)
    (s₀ : M) :
    ∃ W : Set M, ChartBall (E := E) s₀ W ∧ s₀ ∈ W ∧
      ∃ (n : ℕ) (ℓ : M → (Fin n → ℂ) →L[ℂ] V), IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) ℓ W ∧
        (∀ s ∈ W, Function.Injective (ℓ s)) ∧ ∀ s ∈ W, A s ⊆ Set.range (ℓ s) := by
  obtain ⟨U, hUo, hs₀U, n, ℓ, hℓ, hinj, hrange⟩ := hft s₀
  obtain ⟨W, hWb, hs₀W, hWU⟩ := exists_chartBall_subset (E := E) s₀ (hUo.mem_nhds hs₀U)
  exact ⟨W, hWb, hs₀W, n, ℓ, fun v φ => (hℓ v φ).mono hWU, fun s hs => hinj s (hWU hs),
    fun s hs => hrange s (hWU hs)⟩

end Frame

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  {ι : Type*} {F : ι → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module ℂ (F i)]
  [∀ i, Module ℝ (F i)] [∀ i, IsScalarTower ℝ ℂ (F i)] [∀ i, TopologicalSpace (F i)]
  [∀ i, IsTopologicalAddGroup (F i)] [∀ i, ContinuousSMul ℂ (F i)]
  [∀ i, LocallyConvexSpace ℝ (F i)] [∀ i, T2Space (F i)]

/-- Bernstein–Lapid, Appendix A, the local claim. Let `W` be a chart ball with an
injective holomorphic frame `ℓ` whose ranges contain the solutions, and suppose
`W` meets the interior of `M_unq`. Then for any `n` scalar equations `a` and any
`s ∈ W` with `det A(s) ≠ 0`, where `A = scalarMatrix μ ℓ a`, the system has the
unique solution `(det A(s))⁻¹ • adjugateSolution μ c ℓ a s` at `s`. -/
theorem systemSolutions_eq_of_det_ne_zero (hH : HartogsDiagonal E)
    {μ : ∀ i, M → V →L[ℂ] F i} {c : ∀ i, M → F i} (hsys : IsAnalyticSystem 𝓘(ℂ, E) μ c)
    {s₀ : M} {W : Set M} (hWb : ChartBall (E := E) s₀ W) {n : ℕ}
    {ℓ : M → (Fin n → ℂ) →L[ℂ] V} (hℓ : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) ℓ W)
    (hrange : ∀ s ∈ W, systemSolutions μ c s ⊆ Set.range (ℓ s))
    (hint : (W ∩ interior (uniqueSolutionLocus μ c)).Nonempty)
    (a : Fin n → Σ i, (F i →L[ℂ] ℂ)) {s : M} (hsW : s ∈ W)
    (hdet : (scalarMatrix μ ℓ a s).det ≠ 0) :
    systemSolutions μ c s = {((scalarMatrix μ ℓ a s).det)⁻¹ • adjugateSolution μ c ℓ a s} := by
  have hWo := hWb.isOpen
  set f : M → ℂ := fun s => (scalarMatrix μ ℓ a s).det with hf
  set u : M → V := adjugateSolution μ c ℓ a with hu
  have hsol : ∀ t ∈ W, ∀ x ∈ systemSolutions μ c t, f t • x = u t := fun t ht x hx =>
    det_smul_eq_adjugateSolution a (hrange t ht) hx
  -- the scalarized residuals vanish on the interior of `M_unq`, hence on `W`
  have hzero : ∀ i (φ : F i →L[ℂ] ℂ), ∀ t ∈ W, φ (μ i t (u t)) = f t * φ (c i t) := by
    intro i φ t ht
    have hEq := hWb.eqOn_zero (mdifferentiableOn_residual hH hsys hWo hℓ a i φ)
      (hWo.inter isOpen_interior) inter_subset_left hint ?_
    · exact sub_eq_zero.1 (hEq ht)
    · rintro p ⟨hpW, hpP⟩
      obtain ⟨w, hw⟩ := interior_subset hpP
      have hwp : w ∈ systemSolutions μ c p := by rw [hw]; rfl
      have h1 := hsol p hpW w hwp
      show φ (μ i p (u p)) - f p * φ (c i p) = 0
      rw [← h1, map_smul, map_smul, smul_eq_mul, hwp i, sub_self]
  have hw : (f s)⁻¹ • u s ∈ systemSolutions μ c s := by
    intro i
    refine eq_of_forall_clm_apply_eq fun φ => ?_
    rw [map_smul, map_smul, smul_eq_mul, hzero i φ s hsW, ← mul_assoc, inv_mul_cancel₀ hdet,
      one_mul]
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [Set.mem_singleton_iff, ← hsol s hsW x hx, smul_smul, inv_mul_cancel₀ hdet, one_smul]
  · rw [Set.mem_singleton_iff.1 hx]
    exact hw

/-- On a chart ball as in `systemSolutions_eq_of_det_ne_zero`, the
unique-solution locus is the set where some `n × n` determinant
`det (scalarMatrix μ ℓ a s)` does not vanish. -/
theorem mem_uniqueSolutionLocus_iff_exists_det_ne_zero (hH : HartogsDiagonal E)
    {μ : ∀ i, M → V →L[ℂ] F i} {c : ∀ i, M → F i} (hsys : IsAnalyticSystem 𝓘(ℂ, E) μ c)
    {s₀ : M} {W : Set M} (hWb : ChartBall (E := E) s₀ W) {n : ℕ}
    {ℓ : M → (Fin n → ℂ) →L[ℂ] V} (hℓ : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) ℓ W)
    (hinj : ∀ s ∈ W, Function.Injective (ℓ s))
    (hrange : ∀ s ∈ W, systemSolutions μ c s ⊆ Set.range (ℓ s))
    (hint : (W ∩ interior (uniqueSolutionLocus μ c)).Nonempty) {s : M} (hsW : s ∈ W) :
    s ∈ uniqueSolutionLocus μ c ↔
      ∃ a : Fin n → Σ i, (F i →L[ℂ] ℂ), (scalarMatrix μ ℓ a s).det ≠ 0 := by
  refine ⟨fun hs => exists_det_scalarMatrix_ne_zero (hinj s hsW) hs, ?_⟩
  rintro ⟨a, ha⟩
  exact ⟨_, systemSolutions_eq_of_det_ne_zero hH hsys hWb hℓ hrange hint a hsW ha⟩

/-- Bernstein–Lapid, Appendix A, the global step: on a connected manifold, if the
unique-solution locus `M_unq` has nonempty interior, then the closure of its
interior is all of `M`. -/
theorem closure_interior_uniqueSolutionLocus_eq_univ [ConnectedSpace M]
    (hH : HartogsDiagonal E) {μ : ∀ i, M → V →L[ℂ] F i} {c : ∀ i, M → F i}
    (hsys : IsAnalyticSystem 𝓘(ℂ, E) μ c)
    (hft : IsLocallyFiniteType 𝓘(ℂ, E) (systemSolutions μ c))
    (hint : (interior (uniqueSolutionLocus μ c)).Nonempty) :
    closure (interior (uniqueSolutionLocus μ c)) = univ := by
  set P := uniqueSolutionLocus μ c with hP
  have hclopen : IsClopen (closure (interior P)) := by
    refine ⟨isClosed_closure, isOpen_iff_mem_nhds.2 fun s₀ hs₀ => ?_⟩
    obtain ⟨W, hWb, hs₀W, n, ℓ, hℓ, hinj, hrange⟩ := exists_chartBall_frame hft s₀
    have hWo := hWb.isOpen
    obtain ⟨s₁, hs₁W, hs₁P⟩ := mem_closure_iff.1 hs₀ W hWo hs₀W
    obtain ⟨a, ha⟩ := exists_det_scalarMatrix_ne_zero (hinj s₁ hs₁W) (interior_subset hs₁P)
    set f : M → ℂ := fun s => (scalarMatrix μ ℓ a s).det with hf
    have hfh : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f W :=
      mdifferentiableOn_det_scalarMatrix hH hsys hWo hℓ a
    have hNo : IsOpen (W ∩ f ⁻¹' {0}ᶜ) :=
      hfh.continuousOn.isOpen_inter_preimage hWo isOpen_compl_singleton
    have hNP : W ∩ f ⁻¹' {0}ᶜ ⊆ P := fun s hs =>
      ⟨_, systemSolutions_eq_of_det_ne_zero hH hsys hWb hℓ hrange ⟨s₁, hs₁W, hs₁P⟩ a hs.1 hs.2⟩
    refine Filter.mem_of_superset (hWo.mem_nhds hs₀W) fun x hxW => ?_
    rw [mem_closure_iff]
    intro O hO hxO
    by_contra hempty
    have hfO : EqOn f 0 (O ∩ W) := by
      intro y hy
      by_contra hfy
      exact hempty ⟨y, hy.1, interior_maximal hNP hNo ⟨hy.2, hfy⟩⟩
    exact ha (hWb.eqOn_zero hfh (hO.inter hWo) inter_subset_right ⟨x, hxO, hxW⟩ hfO hs₁W)
  exact hclopen.eq_univ ⟨hint.some, subset_closure hint.some_mem⟩

/-- Local data at a point `s₁ ∈ M_unq`: a chart ball `W ∋ s₁` and holomorphic `f`,
`u` on `W` with `f s₁ ≠ 0`, `f s • x = u s` for all solutions `x` at `s ∈ W`, and
the unique solution `(f s)⁻¹ • u s` wherever `f s ≠ 0` on `W`. -/
theorem exists_local_data [ConnectedSpace M] (hH : HartogsDiagonal E)
    {μ : ∀ i, M → V →L[ℂ] F i} {c : ∀ i, M → F i} (hsys : IsAnalyticSystem 𝓘(ℂ, E) μ c)
    (hft : IsLocallyFiniteType 𝓘(ℂ, E) (systemSolutions μ c))
    (hint : (interior (uniqueSolutionLocus μ c)).Nonempty) (s₀ : M) :
    ∃ W : Set M, ChartBall (E := E) s₀ W ∧ s₀ ∈ W ∧
      ∀ s₁ ∈ W ∩ uniqueSolutionLocus μ c,
        ∃ (f : M → ℂ) (u : M → V), MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f W ∧
          IsHolomorphicOn 𝓘(ℂ, E) u W ∧ f s₁ ≠ 0 ∧
          (∀ s ∈ W, ∀ x ∈ systemSolutions μ c s, f s • x = u s) ∧
          ∀ s ∈ W, f s ≠ 0 → systemSolutions μ c s = {(f s)⁻¹ • u s} := by
  obtain ⟨W, hWb, hs₀W, n, ℓ, hℓ, hinj, hrange⟩ := exists_chartBall_frame hft s₀
  have hWo := hWb.isOpen
  have hmeets : (W ∩ interior (uniqueSolutionLocus μ c)).Nonempty := by
    have hs : s₀ ∈ closure (interior (uniqueSolutionLocus μ c)) := by
      rw [closure_interior_uniqueSolutionLocus_eq_univ hH hsys hft hint]
      exact mem_univ s₀
    exact mem_closure_iff.1 hs W hWo hs₀W
  refine ⟨W, hWb, hs₀W, fun s₁ ⟨hs₁W, hs₁P⟩ => ?_⟩
  obtain ⟨a, ha⟩ := exists_det_scalarMatrix_ne_zero (hinj s₁ hs₁W) hs₁P
  exact ⟨fun s => (scalarMatrix μ ℓ a s).det, adjugateSolution μ c ℓ a,
    mdifferentiableOn_det_scalarMatrix hH hsys hWo hℓ a,
    isHolomorphicOn_adjugateSolution hH hsys hWo hℓ a, ha,
    fun s hs x hx => det_smul_eq_adjugateSolution a (hrange s hs) hx,
    fun s hs hfs => systemSolutions_eq_of_det_ne_zero hH hsys hWb hℓ hrange hmeets a hs hfs⟩

/-- The principle of meromorphic continuation, parts (2), (3) and the openness in
part (1), assuming Hartogs's theorem in the diagonal form `HartogsDiagonal E`. -/
theorem exists_holomorphic_meromorphic_of_hartogs [ConnectedSpace M] (hH : HartogsDiagonal E)
    {μ : ∀ i, M → V →L[ℂ] F i} {c : ∀ i, M → F i}
    (hsys : IsAnalyticSystem 𝓘(ℂ, E) μ c)
    (hft : IsLocallyFiniteType 𝓘(ℂ, E) (systemSolutions μ c))
    (hint : (interior (uniqueSolutionLocus μ c)).Nonempty) :
    ∃ v : M → V,
      (∀ s ∈ uniqueSolutionLocus μ c, systemSolutions μ c s = {v s}) ∧
      IsOpen (uniqueSolutionLocus μ c) ∧
      IsHolomorphicOn 𝓘(ℂ, E) v (uniqueSolutionLocus μ c) ∧
      IsMeromorphicOn 𝓘(ℂ, E) v (uniqueSolutionLocus μ c) := by
  classical
  set P := uniqueSolutionLocus μ c with hP
  have hloc := exists_local_data hH hsys hft hint
  have hC := closure_interior_uniqueSolutionLocus_eq_univ hH hsys hft hint
  -- the open set where the local determinant does not vanish lies in `M_unq`
  have hgood : ∀ {W : Set M} {f : M → ℂ} {u : M → V}, IsOpen W →
      MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f W →
      (∀ s ∈ W, f s ≠ 0 → systemSolutions μ c s = {(f s)⁻¹ • u s}) →
      IsOpen (W ∩ f ⁻¹' {0}ᶜ) ∧ W ∩ f ⁻¹' {0}ᶜ ⊆ P := by
    intro W f u hWo hf hsolu
    exact ⟨hf.continuousOn.isOpen_inter_preimage hWo isOpen_compl_singleton,
      fun s hs => ⟨_, hsolu s hs.1 hs.2⟩⟩
  have hmeets : ∀ {W : Set M} {s : M}, IsOpen W → s ∈ W → (W ∩ interior P).Nonempty := by
    intro W s hWo hsW
    have hs : s ∈ closure (interior P) := by rw [hC]; exact mem_univ s
    exact mem_closure_iff.1 hs W hWo hsW
  -- `M_unq` is open
  have hPopen : IsOpen P := by
    refine isOpen_iff_mem_nhds.2 fun s₁ hs₁ => ?_
    obtain ⟨W, hWb, hs₁W, hdata⟩ := hloc s₁
    obtain ⟨f, u, hf, -, hf₁, -, hsolu⟩ := hdata s₁ ⟨hs₁W, hs₁⟩
    obtain ⟨hNo, hNP⟩ := hgood hWb.isOpen hf hsolu
    exact Filter.mem_of_superset (hNo.mem_nhds ⟨hs₁W, hf₁⟩) hNP
  -- the unique solution
  let v : M → V := fun s =>
    if h : s ∈ P then Classical.choose (show ∃ w : V, systemSolutions μ c s = {w} from h) else 0
  have hv : ∀ s ∈ P, systemSolutions μ c s = {v s} := by
    intro s hs
    simp only [v, hs, ↓reduceDIte]
    exact Classical.choose_spec (show ∃ w : V, systemSolutions μ c s = {w} from hs)
  -- `v` is holomorphic on `M_unq`
  have hvhol : IsHolomorphicOn 𝓘(ℂ, E) v P := by
    intro φ s₁ hs₁
    obtain ⟨W, hWb, hs₁W, hdata⟩ := hloc s₁
    obtain ⟨f, u, hf, hu, hf₁, -, hsolu⟩ := hdata s₁ ⟨hs₁W, hs₁⟩
    obtain ⟨hNo, hNP⟩ := hgood hWb.isOpen hf hsolu
    have hs₁N : s₁ ∈ W ∩ f ⁻¹' {0}ᶜ := ⟨hs₁W, hf₁⟩
    have hg : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun s => (f s)⁻¹ * φ (u s))
        (W ∩ f ⁻¹' {0}ᶜ) :=
      ((hf.mono inter_subset_left).inv fun s hs => hs.2).mul ((hu φ).mono inter_subset_left)
    refine ((hg.mdifferentiableAt (hNo.mem_nhds hs₁N)).congr_of_eventuallyEq ?_)
      |>.mdifferentiableWithinAt
    filter_upwards [hNo.mem_nhds hs₁N] with s hs
    have h1 := hv s (hNP hs)
    rw [hsolu s hs.1 hs.2] at h1
    have h2 : v s = (f s)⁻¹ • u s := (Set.singleton_eq_singleton_iff.1 h1).symm
    simp only [h2, map_smul, smul_eq_mul]
  -- meromorphy
  have hdenseP : Dense P := (dense_iff_closure_eq.2 hC).mono interior_subset
  refine ⟨v, hv, hPopen, hvhol, hPopen, hdenseP, hvhol, fun s₀ => ?_⟩
  obtain ⟨W, hWb, hs₀W, hdata⟩ := hloc s₀
  obtain ⟨s₁, hs₁W, hs₁P⟩ := hmeets hWb.isOpen hs₀W
  obtain ⟨f, u, hf, hu, hf₁, hsol, -⟩ := hdata s₁ ⟨hs₁W, interior_subset hs₁P⟩
  refine ⟨W, hWb.isOpen, ⟨⟨s₀, hs₀W⟩, hWb.isPreconnected⟩, hs₀W, f, u, hf, ⟨s₁, hs₁W, hf₁⟩,
    hu, ?_⟩
  rintro s ⟨hsP, hsW⟩
  exact hsol s hsW (v s) (by rw [hv s hsP]; rfl)

end Main

/-- The principle of meromorphic continuation, parts (2), (3) and the openness in
part (1), from Hartogs's theorem in the diagonal form for every finite-dimensional
complex normed space `E` of universe `uE`. -/
theorem meromorphicContinuationHolomorphic_of_hartogs
    (hH : ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E],
      HartogsDiagonal E) :
    MeromorphicContinuationHolomorphicStatement.{uE, uM, uV, uι, uF} := by
  unfold MeromorphicContinuationHolomorphicStatement
  intro E _ _ _ M _ _ _ _ V _ _ _ _ _ _ _ _ _ ι F _ _ _ _ _ _ _ _ _ μ c hsys hft hint
  exact exists_holomorphic_meromorphic_of_hartogs (hH E) hsys hft hint

end Langlands.Analysis.Meromorphic
