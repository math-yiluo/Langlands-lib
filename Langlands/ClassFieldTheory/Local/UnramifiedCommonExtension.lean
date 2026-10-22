import Langlands.Galois.Local.UnramifiedCriterionStatement

/-! # A common unramified overfield from the canonical inertia criterion -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

open Langlands.LocalClassField

/-- The actual compositum of two finite unramified Galois intermediate fields,
with its inclusions and unramified certificate. The arithmetic inertia criterion
is an explicit input; this construction does not prove that criterion. -/
def commonUnramifiedExtension
    (hCriterion : Langlands.PadicField.CanonicalUnramifiedCriterion.{u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (L M : FiniteIntermediateExtension F.Carrier)
    [IsGalois F.Carrier L.field] [IsGalois F.Carrier M.field]
    (hL : F.canonicalTopologicalData.ramificationIndex =
      (L.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex)
    (hM : F.canonicalTopologicalData.ramificationIndex =
      (M.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex) :
    {N : FiniteIntermediateExtension F.Carrier //
      IsGalois F.Carrier N.field ∧ L.field ≤ N.field ∧ M.field ≤ N.field ∧
        F.canonicalTopologicalData.ramificationIndex =
          (N.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex} := by
  letI : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let N : FiniteIntermediateExtension F.Carrier := ⟨L.field ⊔ M.field, inferInstance⟩
  haveI : IsGalois F.Carrier N.field := { }
  refine ⟨N, inferInstance, le_sup_left, le_sup_right, ?_⟩
  apply (hCriterion p F N).mpr
  change F.absoluteInertia F.canonicalTopologicalData ≤
    (L.field ⊔ M.field).fixingSubgroup
  rw [IntermediateField.fixingSubgroup_sup]
  exact le_inf ((hCriterion p F L).mp hL) ((hCriterion p F M).mp hM)

/-- The selected common field is the lattice supremum, without an arbitrary
choice of a larger extension. -/
@[simp] theorem commonUnramifiedExtension_field
    (hCriterion : Langlands.PadicField.CanonicalUnramifiedCriterion.{u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (L M : FiniteIntermediateExtension F.Carrier)
    [IsGalois F.Carrier L.field] [IsGalois F.Carrier M.field]
    (hL : F.canonicalTopologicalData.ramificationIndex =
      (L.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex)
    (hM : F.canonicalTopologicalData.ramificationIndex =
      (M.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex) :
    (commonUnramifiedExtension hCriterion F L M hL hM).val.field =
      L.field ⊔ M.field := rfl

end Langlands.ClassFieldTheory.Local
