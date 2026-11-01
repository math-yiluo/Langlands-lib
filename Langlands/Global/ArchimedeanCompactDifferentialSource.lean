import Langlands.Global.ArchimedeanCompactDifferentialGeneratedModule
import Langlands.Global.ArchimedeanCompactHomGeneration

/-! # A finite stable source generating the actual differential module -/

noncomputable section
universe u w
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

omit [NumberField K] in
/-- The full action span is the complex scalar restriction of the enveloping span,
for any compatible genuine enveloping module. -/
theorem full_enveloping_actionSpan_eq_span
    {V : Type w} [AddCommGroup V] [Module ℂ V]
    [Module (EnvelopingAlgebra K n) V] [IsScalarTower ℂ (EnvelopingAlgebra K n) V]
    (S : Submodule ℂ V) :
    (⊤ : Submodule ℂ (EnvelopingAlgebra K n)) • S =
      (Submodule.span (EnvelopingAlgebra K n) (S : Set V)).restrictScalars ℂ := by
  have hstable : ∀ (a : EnvelopingAlgebra K n) {v : V},
      v ∈ (⊤ : Submodule ℂ (EnvelopingAlgebra K n)) • S →
      a • v ∈ (⊤ : Submodule ℂ (EnvelopingAlgebra K n)) • S := by
    intro a v hv
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro b hb v hv
      simpa only [mul_smul] using
        (Submodule.smul_mem_smul (I := (⊤ : Submodule ℂ (EnvelopingAlgebra K n)))
          (r := a * b) Submodule.mem_top hv)
    · intro v w hv hw
      simpa only [smul_add] using Submodule.add_mem _ hv hw
  apply le_antisymm
  · apply Submodule.smul_le.mpr
    intro a ha v hv
    exact (Submodule.span (EnvelopingAlgebra K n) (S : Set V)).smul_mem
      a (Submodule.subset_span hv)
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      simpa only [one_smul] using
        (Submodule.smul_mem_smul (I := (⊤ : Submodule ℂ (EnvelopingAlgebra K n)))
          (r := 1) Submodule.mem_top hv)
    | zero => exact Submodule.zero_mem _
    | add v w hv hw ihv ihw => exact Submodule.add_mem _ ihv ihw
    | smul a v hv ih => exact hstable a ih

/-- The actual finite compact orbit, included into its genuine generated module. -/
def compactDifferentialSourceMap (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    (Fin (compactOrbitSource K n f hf).dim → ℂ) →ₗ[ℂ]
      compactDifferentialGeneratedModule K n f :=
  ((Langlands.FiniteVectors.orbitSpan (compactAction K n) f).inclusionSpan
      (EnvelopingAlgebra K n)).comp (compactOrbitModelEquiv K n f hf).toLinearMap

@[simp]
theorem compactDifferentialSourceMap_val (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (v : Fin (compactOrbitSource K n f hf).dim → ℂ) :
    (compactDifferentialSourceMap K n f hf v).val = compactOrbitSourceMap K n f hf v := rfl

/-- The lifted source intertwines the actual whole compact representations. -/
theorem compactDifferentialSourceMap_equivariant (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (k : standardInfiniteCompact K n) (v : Fin (compactOrbitSource K n f hf).dim → ℂ) :
    compactDifferentialSourceMap K n f hf ((compactOrbitSource K n f hf).toRepresentation k v) =
      compactDifferentialGeneratedAction K n f k (compactDifferentialSourceMap K n f hf v) := by
  apply Subtype.ext
  exact compactOrbitSourceMap_equivariant K n f hf k v

/-- The lifted source generates the entire genuine enveloping module. -/
theorem compactDifferentialSourceMap_generates (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) :
    (⊤ : Submodule ℂ (EnvelopingAlgebra K n)) •
      LinearMap.range (compactDifferentialSourceMap K n f hf) = ⊤ := by
  have hrange : LinearMap.range (compactDifferentialSourceMap K n f hf) =
      LinearMap.range ((Langlands.FiniteVectors.orbitSpan (compactAction K n) f).inclusionSpan
        (EnvelopingAlgebra K n)) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact ⟨compactOrbitModelEquiv K n f hf v, rfl⟩
    · rintro _ ⟨v, rfl⟩
      refine ⟨(compactOrbitModelEquiv K n f hf).symm v, ?_⟩
      change (Langlands.FiniteVectors.orbitSpan (compactAction K n) f).inclusionSpan
        (EnvelopingAlgebra K n) (compactOrbitModelEquiv K n f hf
          ((compactOrbitModelEquiv K n f hf).symm v)) = _
      rw [LinearEquiv.apply_symm_apply]
  rw [full_enveloping_actionSpan_eq_span K n, hrange]
  change (Submodule.span (EnvelopingAlgebra K n)
    (Set.range ((Langlands.FiniteVectors.orbitSpan (compactAction K n) f).inclusionSpan
      (EnvelopingAlgebra K n)))).restrictScalars ℂ = ⊤
  rw [Submodule.span_range_inclusionSpan]
  rfl

/-- The image inside the generated module retains actual compact-generator stability. -/
theorem compactDifferentialSourceMap_range_stable (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (X : CompactComplexLieAlgebra K n)
    (v : compactDifferentialGeneratedModule K n f)
    (hv : v ∈ LinearMap.range (compactDifferentialSourceMap K n f hf)) :
    compactEnvelopingGenerator K n X • v ∈
      LinearMap.range (compactDifferentialSourceMap K n f hf) := by
  obtain ⟨x, hx⟩ := hv
  have hxval : compactOrbitSourceMap K n f hf x = v.val := congrArg Subtype.val hx
  obtain ⟨y, hy⟩ := compactOrbitSourceMap_range_stable K n f hf X v.val ⟨x, hxval⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  exact hy

/-- Each internal isotypic span of the actual generated module has a finite
covering by full center orbits of basis evaluations. -/
theorem exists_finite_central_cover_generatedModule_isotypic
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (σ : ContinuousCompactRep K n) :
    ∃ (m : ℕ) (F : Fin m → (Fin σ.dim → ℂ) →ₗ[ℂ]
      compactDifferentialGeneratedModule K n f),
      Langlands.CompactSplitting.isotypicPart σ.toRepresentation
        (compactDifferentialGeneratedAction K n f) ≤
          compactHomCentralEvaluationSpan K n σ F := by
  exact exists_finite_central_cover_of_generated_isotypic K n σ (compactOrbitSource K n f hf)
    (compactDifferentialSourceMap K n f hf) (compactDifferentialGeneratedAction K n f)
    (compactDifferentialSourceMap_equivariant K n f hf)
    (generatedAction_enveloping_compatible K n f)
    (compactDifferentialSourceMap_range_stable K n f hf)
    (compactDifferentialSourceMap_generates K n f hf)

end Langlands.Global.ArchimedeanGL
