import Langlands.Global.ArchimedeanCompactTypeCentralSpanStatement
import Langlands.Global.ArchimedeanCompactDifferentialSource
import Langlands.Representation.IsotypicRestriction

/-! # Finite central coverings of actual generated compact types -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The actual generated module includes equivariantly into the ambient compact action. -/
def compactDifferentialGeneratedInclusion (f : DerivativeSmoothFunctions K n) :
    (compactDifferentialGeneratedAction K n f).IntertwiningMap (compactAction K n) where
  toLinearMap := (compactDifferentialGeneratedModule K n f).subtype.restrictScalars ℂ
  isIntertwining' _k := by ext v; rfl

@[simp]
theorem compactDifferentialGeneratedInclusion_apply (f : DerivativeSmoothFunctions K n)
    (v : compactDifferentialGeneratedModule K n f) :
    compactDifferentialGeneratedInclusion K n f v = v.val := rfl

/-- The inclusion range is precisely the published generated complex span. -/
theorem compactDifferentialGeneratedInclusion_range (f : DerivativeSmoothFunctions K n) :
    LinearMap.range (compactDifferentialGeneratedInclusion K n f).toLinearMap =
      compactDifferentialGeneratedSpan K n f := by
  rw [← compactDifferentialGeneratedModule_restrictScalars K n f]
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact w.property
  · intro hv
    exact ⟨⟨v, hv⟩, rfl⟩

/-- The internal isotypic part maps exactly to the ambient compact-type intersection. -/
theorem generatedModule_isotypic_map (f : DerivativeSmoothFunctions K n)
    (σ : CompactType K n) :
    (Langlands.CompactSplitting.isotypicPart σ.toRepresentation
      (compactDifferentialGeneratedAction K n f)).map
        (compactDifferentialGeneratedInclusion K n f).toLinearMap =
      compactTypeSubmodule σ ⊓ compactDifferentialGeneratedSpan K n f := by
  let : σ.toRepresentation.IsIrreducible := σ.isIrreducible
  rw [Langlands.CompactSplitting.isotypicPart_map_of_injective σ.toRepresentation
    (compactDifferentialGeneratedAction K n f) (compactAction K n)
    (compactDifferentialGeneratedInclusion K n f) Subtype.val_injective,
    compactDifferentialGeneratedInclusion_range]
  rfl

/-- Full center orbits in the generated module map to the actual smooth center orbits. -/
theorem generatedModule_centerOrbit_map (f : DerivativeSmoothFunctions K n)
    (v : compactDifferentialGeneratedModule K n f) :
    (Submodule.span ℂ (Set.range fun z : EnvelopingCenter K n =>
      (z : EnvelopingAlgebra K n) • v)).map
        (compactDifferentialGeneratedInclusion K n f).toLinearMap =
      (centerOrbitSpan K n (toSmooth K n v.val)).map (toSmooth K n).symm.toLinearMap := by
  change (Submodule.span ℂ (Set.range fun z : EnvelopingCenter K n =>
      (z : EnvelopingAlgebra K n) • v)).map
        (compactDifferentialGeneratedInclusion K n f).toLinearMap =
      (Submodule.span ℂ (Set.range fun z : EnvelopingCenter K n =>
        centerAction K n z (toSmooth K n v.val))).map (toSmooth K n).symm.toLinearMap
  rw [Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
  rfl

/-- Every actual generated compact type has a finite covering by full center orbits. -/
theorem compactTypeCentralSpan : CompactTypeCentralSpanStatement K n := by
  intro f hf σ
  change ∃ (l : ℕ) (v : Fin l → compactDifferentialGeneratedSpan K n f),
    compactTypeSubmodule σ ⊓ compactDifferentialGeneratedSpan K n f ≤
      ⨆ i : Fin l, (centerOrbitSpan K n (toSmooth K n (v i).val)).map
        (toSmooth K n).symm.toLinearMap
  obtain ⟨m, F, hF⟩ := exists_finite_central_cover_generatedModule_isotypic K n f hf
    σ.toContinuousCompactRep
  let v : Fin (m * σ.dim) → compactDifferentialGeneratedSpan K n f := fun i =>
    ⟨(F (finProdFinEquiv.symm i).1 (Pi.single (finProdFinEquiv.symm i).2 1)).val, by
      rw [← compactDifferentialGeneratedModule_restrictScalars K n f]
      exact (F (finProdFinEquiv.symm i).1 (Pi.single (finProdFinEquiv.symm i).2 1)).property⟩
  refine ⟨m * σ.dim, v, ?_⟩
  rw [← generatedModule_isotypic_map K n f σ]
  apply le_trans (Submodule.map_mono hF)
  rw [compactHomCentralEvaluationSpan, Submodule.map_iSup]
  apply iSup_le
  intro p
  rw [generatedModule_centerOrbit_map]
  apply le_iSup_of_le (finProdFinEquiv p)
  simp only [v, Equiv.symm_apply_apply]
  exact le_rfl

end Langlands.Global.ArchimedeanGL
