import Langlands.Galois.Local.TotalRamifiedInertiaDisjointStatement
import Langlands.Galois.Local.InertiaFixedFieldUnramifiedProof
import Langlands.ClassFieldTheory.Local.TotalUnramifiedCompositumProof

/-! # Disjointness from the actual inertia fixed field -/

namespace Langlands.PadicField

universe u

/-- A finite totally ramified Galois field is linearly disjoint from the
actual canonical inertia fixed field. -/
theorem totallyRamifiedInertiaDisjoint :
    TotallyRamifiedInertiaDisjoint.{u} := by
  intro p _ F D _ hD
  classical
  let U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
  let : Algebra.IsIntegral F.Carrier U.toSubalgebra :=
    Algebra.IsIntegral.of_injective U.toSubalgebra.val Subtype.val_injective
  apply IntermediateField.linearDisjoint_iff'.mpr
  apply Subalgebra.LinearDisjoint.of_linearDisjoint_finite_right
  intro B hBU _
  obtain ⟨s, hs⟩ : B.toSubmodule.FG := .of_finite
  have hsU : ∀ x ∈ s, x ∈ U := by
    intro x hx
    apply hBU
    change x ∈ B.toSubmodule
    rw [← hs]
    exact Submodule.subset_span hx
  obtain ⟨E, hGalois, hE, hsE⟩ :=
    (inertiaFixedFieldUnramifiedExhaustion p F).2 s hsU
  let := hGalois
  have hBE : B.toSubmodule ≤ E.field.toSubalgebra.toSubmodule := by
    rw [← hs, Submodule.span_le]
    exact hsE
  have hd := (Langlands.LocalClassField.totalUnramifiedCompositum p F D E hD hE.symm).1
  exact Submodule.LinearDisjoint.of_le_right_of_flat
    (IntermediateField.linearDisjoint_iff'.mp hd) hBE

end Langlands.PadicField
