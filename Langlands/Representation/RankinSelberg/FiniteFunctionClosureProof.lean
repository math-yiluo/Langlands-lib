import Langlands.Representation.RankinSelberg.FiniteFunctionClosureStatement
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.RingTheory.Noetherian.Basic

namespace Langlands.RankinSelberg

universe uG uH

/-- Products, continuous pullbacks, and characters preserve the finite-function
condition used in coefficient-torus expansions. -/
theorem finiteFunctionClosure (G : Type uG) (H : Type uH)
    [Monoid G] [Monoid H] [TopologicalSpace G] [TopologicalSpace H] :
    FiniteFunctionClosureStatement G H := by
  unfold FiniteFunctionClosureStatement
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro f g hf hg
    refine ⟨hf.1.mul hg.1, ?_⟩
    apply (Submodule.fg_iff_finiteDimensional _).mp
    have hfg := ((Submodule.fg_iff_finiteDimensional _).mpr hf.2).mul
      ((Submodule.fg_iff_finiteDimensional _).mpr hg.2)
    apply hfg.of_le
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨b, rfl⟩)
      (Submodule.subset_span ⟨b, rfl⟩)
  · intro h hh f hf
    refine ⟨hf.1.comp hh, ?_⟩
    let pull : (G → ℂ) →ₗ[ℂ] (H → ℂ) :=
      { toFun := fun v a => v (h a)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    apply (Submodule.fg_iff_finiteDimensional _).mp
    have hmap := ((Submodule.fg_iff_finiteDimensional _).mpr hf.2).map pull
    apply hmap.of_le
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    refine Submodule.mem_map.mpr ⟨(fun a => f (h b * a)),
      Submodule.subset_span ⟨h b, rfl⟩, ?_⟩
    ext a
    simp [pull, map_mul]
  · intro χ hχ
    refine ⟨hχ, ?_⟩
    apply (Submodule.fg_iff_finiteDimensional _).mp
    apply (Submodule.fg_span_singleton (R := ℂ) (χ : G → ℂ)).of_le
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    have hmem := (Submodule.span ℂ {(χ : G → ℂ)}).smul_mem (χ b)
      (Submodule.subset_span (Set.mem_singleton (χ : G → ℂ)))
    have heq : (fun a => χ (b * a)) = χ b • (χ : G → ℂ) := by
      ext a
      exact map_mul χ b a
    change (fun a => χ (b * a)) ∈ Submodule.span ℂ {(χ : G → ℂ)}
    rw [heq]
    exact hmem

end Langlands.RankinSelberg
