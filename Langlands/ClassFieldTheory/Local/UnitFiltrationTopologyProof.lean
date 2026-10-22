import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof

/-! Compact lifting for the actual unit filtration. -/

namespace Langlands.LocalClassField

universe u v

/-- The compact lifting argument, with its structural prerequisites explicit. -/
theorem unitFiltrationCompactLifting_of_structural
    (hF : UnitFiltrationStructuralLaws.{u})
    (hE : UnitFiltrationStructuralLaws.{v}) : UnitFiltrationCompactLifting.{u,v} := by
  intro p hp F E T S
  let := T.topology
  let := S.topology
  let := T.valuativeRel
  let := S.valuativeRel
  let := T.localField
  let := S.localField
  intro f hpres happ n
  obtain ⟨hTc, hTa, hTs, _⟩ := hF p F T
  obtain ⟨hSc, hSa, _, _⟩ := hE p E S
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hpres n x hx
  · intro y hy
    have happrox : ∀ k : ℕ, ∃ x : E.Carrierˣ,
        x ∈ S.unitFiltration n ∧ y * (f x)⁻¹ ∈ T.unitFiltration (n + k) := by
      intro k
      induction k with
      | zero =>
        refine ⟨1, (S.unitFiltration n).one_mem, ?_⟩
        simpa using hy
      | succ k ih =>
        obtain ⟨x, hx, herr⟩ := ih
        obtain ⟨z, hz, hnew⟩ := happ (n + k) (y * (f x)⁻¹) herr
        refine ⟨x * z, (S.unitFiltration n).mul_mem hx
          (hSa (Nat.le_add_right n k) hz), ?_⟩
        simpa only [Nat.add_succ, map_mul, mul_inv_rev, mul_assoc,
          mul_left_comm, mul_comm] using hnew
    let C : ℕ → Set E.Carrierˣ := fun k =>
      {x | x ∈ S.unitFiltration n ∧ y * (f x)⁻¹ ∈ T.unitFiltration (n + k)}
    have hCclosed (k : ℕ) : IsClosed (C k) :=
      (hSc n).2.inter ((hTc (n + k)).2.preimage
        (continuous_const.mul f.continuous.inv))
    have hCcompact : IsCompact (C 0) :=
      (hSc n).1.of_isClosed_subset (hCclosed 0) (fun _ hx => hx.1)
    have hCstep (k : ℕ) : C (k + 1) ⊆ C k := by
      intro x hx
      exact ⟨hx.1, hTa (Nat.le_succ (n + k)) hx.2⟩
    obtain ⟨x, hx⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCstep
        happrox hCcompact hCclosed
    have hxC (k : ℕ) : x ∈ C k := Set.mem_iInter.mp hx k
    have herr : y * (f x)⁻¹ = 1 := hTs _ (fun k =>
      hTa (Nat.le_add_left k n) (hxC k).2)
    exact ⟨x, (hxC 0).1, (mul_inv_eq_one.mp herr).symm⟩

/-- Compact lifting for arbitrary supplied local-field data in independent universes. -/
theorem unitFiltrationCompactLifting : UnitFiltrationCompactLifting.{u, v} :=
  unitFiltrationCompactLifting_of_structural
    unitFiltrationStructuralLaws.{u} unitFiltrationStructuralLaws.{v}

/-- The complete structural and compact lifting bundle for the actual unit filtration. -/
theorem unitFiltrationTopologyTheorems : UnitFiltrationTopologyTheorems.{u, v} :=
  ⟨unitFiltrationStructuralLaws.{u}, unitFiltrationStructuralLaws.{v},
    unitFiltrationCompactLifting.{u, v}⟩

end Langlands.LocalClassField
