import Langlands.Representation.Compact.CompactRepresentationCoefficientCriterionProof

/-! # Finite-type compact representations are admissible -/

noncomputable section
universe u v

namespace Langlands.Renard.CompactRepresentation

open MeasureTheory TopologicalSpace

/-- Renard IV.1.3, Proposition, with the published group-algebra finite-type condition. -/
theorem compactFiniteTypeAdmissible : CompactFiniteTypeAdmissibleStatement.{u, v} := by
  intro G _ _ _ _ _ _ π hc hfinite
  classical
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  let := hfinite
  obtain ⟨m, x, hx⟩ := Module.Finite.exists_fin
    (R := MonoidAlgebra ℂ G) (M := π.representation.asModule)
  refine ⟨π.isSmooth, fun L => ?_⟩
  obtain ⟨K, hKL, hK, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ L
  let P := Hecke.fixedProjection μ π.representation π.isSmooth K hK
  let E : Fin m → Submodule ℂ (fixedVectors π.representation K.toSubgroup) := fun i =>
    Submodule.span ℂ (Set.range fun g : G => P (π.representation g (x i)))
  let (i : Fin m) : FiniteDimensional ℂ (E i) :=
    finiteDimensional_span_projectedOrbit μ π.representation π.isSmooth hc K hK (x i)
  let F : Submodule ℂ (fixedVectors π.representation K.toSubgroup) := ⨆ i, E i
  let : FiniteDimensional ℂ F := inferInstance
  let S : Subrepresentation π.representation :=
    { toSubmodule := ⨅ g : G, F.comap (P.comp (π.representation g))
      apply_mem_toSubmodule := fun h y hy => by
        simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply] at hy ⊢
        intro g
        simpa only [map_mul, Module.End.mul_apply] using hy (g * h) }
  have hgen : (⊤ : Submodule (MonoidAlgebra ℂ G) π.representation.asModule) ≤ S.asSubmodule := by
    rw [← hx]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change x i ∈ S.toSubmodule
    apply (Submodule.mem_iInf (fun g : G => F.comap (P.comp (π.representation g)))).mpr
    intro g
    exact (le_iSup E i) (Submodule.subset_span ⟨g, rfl⟩)
  let f : fixedVectors π.representation K.toSubgroup →ₗ[ℂ] F :=
    { toFun := fun y => ⟨y, by
        have hy : y.val ∈ S.toSubmodule := hgen (by trivial)
        have hy1 : P (π.representation 1 y.val) ∈ F := ((Submodule.mem_iInf _).mp hy) 1
        simpa only [P, map_one, Module.End.one_apply, Hecke.fixedProjection_fixed] using hy1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hfin : FiniteDimensional ℂ (fixedVectors π.representation K.toSubgroup) :=
    FiniteDimensional.of_injective f (fun x y h =>
      congrArg (fun z : F => z.val) h)
  let := hfin
  apply Submodule.finiteDimensional_of_le (S₂ := fixedVectors π.representation K.toSubgroup)
  intro y hy k
  exact hy ⟨k.val, hKL k.property⟩

end Langlands.Renard.CompactRepresentation
