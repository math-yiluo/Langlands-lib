import Langlands.ClassFieldTheory.Local.NYLL.SuppliedUnramifiedStatement
import Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof

/-! # The NYLL unramified class for supplied local-field data: proof -/

namespace Langlands.LocalClassField.NYLL

universe u v

open scoped ValuativeRel

/-- Mathlib's integer algebra from the valuation extension is the explicit
supplied integer algebra, so finiteness and the ramification index transfer. -/
theorem suppliedUnramifiedValuedExtension :
    SuppliedUnramifiedValuedExtensionStatement.{u, v} := by
  intro p _ F E _ _ _ TF TE
  let := TF.topology
  let := TF.valuativeRel
  let := TF.localField
  let := TE.topology
  let := TE.valuativeRel
  let := TE.localField
  intro hext
  have halg : Valuation.HasExtension.instAlgebraInteger =
      PadicField.TopologicalData.relativeIntegerAlgebra TF TE :=
    Algebra.algebra_ext _ _ fun _ => rfl
  refine ⟨?_, fun {hfin} => ?_⟩
  · have h := (relativeIntegerStructure p F E TF TE).2
    rw [← halg] at h
    exact h
  · constructor
    · intro h
      have h1 := h.maximalIdeal_ramificationIdx_eq_one
      rw [halg] at h1
      exact h1
    · intro h
      refine ⟨?_⟩
      rw [halg]
      exact h

end Langlands.LocalClassField.NYLL
