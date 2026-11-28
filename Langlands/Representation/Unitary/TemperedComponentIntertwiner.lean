import Langlands.Representation.Unitary.TemperedComponentAlgebra

/-! # An equivariant map from bounded smoothed maps

Let `σ` be a jointly continuous representation on `V`, `π_W` one on `W`, `ψ_k` a family of test
functions containing an approximate identity `χ_n = ψ_{k(n)}`, and `B_k : V → W` bounded maps with
values in a closed `π_W`-invariant subspace `W₀`, satisfying

`B_{k(n)} σ(a) σ(ψ_k) = π_W(χ_n) π_W(a) B_k`  for all words `a`.

On `D = span {σ(a) σ(ψ_k) v}` the assignment `J (σ(a) σ(ψ_k) v) = π_W(a) B_k v` is well defined:
if a combination of the generators `σ(a) σ(ψ_k) v` vanishes in `V`, applying each `B_{k(n)}` and
the relation shows that `π_W(χ_n)` kills the corresponding combination of the values
`π_W(a) B_k v` in `W`, and since `π_W(χ_n) w → w` that combination vanishes. Extended linearly to
`V`, `J` is equivariant on `D`, bounded on each family `u ↦ σ(φ) σ(ψ_k) u`, nonzero on `D` if some
`B_k` is nonzero, and satisfies `J(D) ⊆ W₀`.
-/

noncomputable section

open MeasureTheory Filter Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Analysis.TemperedComponent

open Langlands.Archimedean

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

theorem exists_intertwiner (σ : G →* (V →L[ℂ] V)) (hσ : IsContinuousRepresentation σ)
    (πW : G →* (W →L[ℂ] W)) (hπW : IsContinuousRepresentation πW)
    {κ : Type*} (ψ : κ → G → ℂ) (hψ : ∀ k, IsTestFunction (ψ k)) (nIdx : ℕ → κ)
    (hχ : IsApproxIdentity μ fun n => ψ (nIdx n)) (B : κ → V →L[ℂ] W)
    (W₀ : Submodule ℂ W) (hW₀c : IsClosed (W₀ : Set W)) (hW₀ : ∀ g, ∀ w ∈ W₀, πW g w ∈ W₀)
    (hBW₀ : ∀ k v, B k v ∈ W₀)
    (hKR : ∀ (n : ℕ) (a : Word G) (k : κ) (v : V),
      B (nIdx n) (wordOp μ σ hσ a (testOp μ σ hσ (ψ k) (hψ k) v)) =
        testOp μ πW hπW (ψ (nIdx n)) (hψ (nIdx n)) (wordOp μ πW hπW a (B k v)))
    (hne : ∃ k v, B k v ≠ 0) :
    ∃ (D : Submodule ℂ V) (J : V →ₗ[ℂ] W),
      (∀ g, ∀ d ∈ D, σ g d ∈ D ∧ J (σ g d) = πW g (J d)) ∧
      (∀ (φ : G → ℂ) (hφ : IsTestFunction φ),
        (∀ d ∈ D, testOp μ σ hσ φ hφ d ∈ D ∧
          J (testOp μ σ hσ φ hφ d) = testOp μ πW hπW φ hφ (J d)) ∧
        ∀ k, ∃ C : ℝ, ∀ u : V, testOp μ σ hσ φ hφ (testOp μ σ hσ (ψ k) (hψ k) u) ∈ D ∧
          ‖J (testOp μ σ hσ φ hφ (testOp μ σ hσ (ψ k) (hψ k) u))‖ ≤ C * ‖u‖) ∧
      (∃ d ∈ D, J d ≠ 0) ∧
      ∀ d ∈ D, J d ∈ W₀ := by
  let δ : Word G × κ × V → V := fun i =>
    wordOp μ σ hσ i.1 (testOp μ σ hσ (ψ i.2.1) (hψ i.2.1) i.2.2)
  let γ : Word G × κ × V → W := fun i => wordOp μ πW hπW i.1 (B i.2.1 i.2.2)
  let Lδ := Finsupp.linearCombination ℂ δ
  let Lγ := Finsupp.linearCombination ℂ γ
  have hker : LinearMap.ker Lδ ≤ LinearMap.ker Lγ := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have hzero : ∀ n, testOp μ πW hπW (ψ (nIdx n)) (hψ (nIdx n)) (Lγ f) = 0 := fun n => by
      have h1 := Finsupp.apply_linearCombination ℂ
        (testOp μ πW hπW (ψ (nIdx n)) (hψ (nIdx n))).toLinearMap γ f
      have h2 := Finsupp.apply_linearCombination ℂ (B (nIdx n)).toLinearMap δ f
      have hcomp : (testOp μ πW hπW (ψ (nIdx n)) (hψ (nIdx n))).toLinearMap ∘ γ =
          (B (nIdx n)).toLinearMap ∘ δ := by
        funext i
        exact (hKR n i.1 i.2.1 i.2.2).symm
      change (testOp μ πW hπW (ψ (nIdx n)) (hψ (nIdx n))).toLinearMap (Lγ f) = 0
      rw [h1, hcomp, ← h2]
      change B (nIdx n) (Lδ f) = 0
      rw [hf, map_zero]
    have hlim := hχ.tendsto πW hπW (Lγ f)
    simp only [hzero] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  let D : Submodule ℂ V := LinearMap.range Lδ
  let J₀ : D →ₗ[ℂ] W :=
    ((LinearMap.ker Lδ).liftQ Lγ hker).comp Lδ.quotKerEquivRange.symm.toLinearMap
  have hJ₀ : ∀ f, J₀ ⟨Lδ f, LinearMap.mem_range_self Lδ f⟩ = Lγ f := fun f => by
    change (LinearMap.ker Lδ).liftQ Lγ hker
      (Lδ.quotKerEquivRange.symm ⟨Lδ f, LinearMap.mem_range_self Lδ f⟩) = Lγ f
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  obtain ⟨J, hJ⟩ := LinearMap.exists_extend J₀
  have hJ' : ∀ f, J (Lδ f) = Lγ f := fun f => by
    rw [← hJ₀ f, ← hJ]
    rfl
  -- prepending a letter
  have hprep : ∀ (l : G ⊕ TestFn G) (f : Word G × κ × V →₀ ℂ),
      letterOp μ σ hσ l (Lδ f) = Lδ (Finsupp.mapDomain (fun i => (l :: i.1, i.2)) f) ∧
      letterOp μ πW hπW l (Lγ f) = Lγ (Finsupp.mapDomain (fun i => (l :: i.1, i.2)) f) := by
    intro l f
    constructor
    · rw [Finsupp.linearCombination_mapDomain]
      exact Finsupp.apply_linearCombination ℂ (letterOp μ σ hσ l).toLinearMap δ f
    · rw [Finsupp.linearCombination_mapDomain]
      exact Finsupp.apply_linearCombination ℂ (letterOp μ πW hπW l).toLinearMap γ f
  have hletter : ∀ (l : G ⊕ TestFn G) (d : V), d ∈ D →
      letterOp μ σ hσ l d ∈ D ∧ J (letterOp μ σ hσ l d) = letterOp μ πW hπW l (J d) := by
    rintro l _ ⟨f, rfl⟩
    obtain ⟨h1, h2⟩ := hprep l f
    refine ⟨h1 ▸ LinearMap.mem_range_self Lδ _, ?_⟩
    rw [h1, hJ', hJ', h2]
  refine ⟨D, J, fun g d hd => hletter (Sum.inl g) d hd, fun φ hφ => ⟨fun d hd =>
    hletter (Sum.inr ⟨φ, hφ⟩) d hd, fun k => ?_⟩, ?_, ?_⟩
  · refine ⟨‖testOp μ πW hπW φ hφ‖ * ‖B k‖, fun u => ?_⟩
    have hδ : testOp μ σ hσ φ hφ (testOp μ σ hσ (ψ k) (hψ k) u) =
        Lδ (Finsupp.single ([Sum.inr ⟨φ, hφ⟩], k, u) 1) := by
      rw [Finsupp.linearCombination_single, one_smul]
      simp only [δ, wordOp_cons, wordOp_nil, mul_one]
      rfl
    refine ⟨hδ ▸ LinearMap.mem_range_self Lδ _, ?_⟩
    rw [hδ, hJ', Finsupp.linearCombination_single, one_smul]
    simp only [γ, wordOp_cons, wordOp_nil, mul_one]
    calc ‖letterOp μ πW hπW (Sum.inr ⟨φ, hφ⟩) (B k u)‖
        ≤ ‖testOp μ πW hπW φ hφ‖ * ‖B k u‖ := (testOp μ πW hπW φ hφ).le_opNorm _
      _ ≤ ‖testOp μ πW hπW φ hφ‖ * (‖B k‖ * ‖u‖) :=
          mul_le_mul_of_nonneg_left ((B k).le_opNorm u) (norm_nonneg _)
      _ = _ := by ring
  · obtain ⟨k, v, hkv⟩ := hne
    have hlim := hχ.tendsto πW hπW (B k v)
    obtain ⟨n, hn⟩ := (hlim.eventually_ne hkv).exists
    refine ⟨Lδ (Finsupp.single ([Sum.inr ⟨ψ (nIdx n), hψ (nIdx n)⟩], k, v) 1),
      LinearMap.mem_range_self Lδ _, ?_⟩
    rw [hJ', Finsupp.linearCombination_single, one_smul]
    simp only [γ, wordOp_cons, wordOp_nil, mul_one]
    exact hn
  · rintro _ ⟨f, rfl⟩
    rw [hJ']
    have hspan : LinearMap.range Lγ ≤ W₀ := by
      rw [Finsupp.range_linearCombination, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact wordOp_mem πW hπW W₀ hW₀c hW₀ i.1 (hBW₀ i.2.1 i.2.2)
    exact hspan (LinearMap.mem_range_self Lγ f)

end Langlands.Analysis.TemperedComponent
