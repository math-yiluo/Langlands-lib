import Langlands.Representation.RankinSelberg.RootTorusProductStatement
import Langlands.Representation.RankinSelberg.RootFiniteFunctionProof
import Langlands.Representation.RankinSelberg.RootSchwartzProof
import Langlands.LocalField.Topology

namespace Langlands.RankinSelberg

open HarmonicAnalysis
open scoped BigOperators

universe uF

/-- The finite-function family in the root-coordinate product is independent
of all test data. -/
theorem rootTorusProduct {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    RootTorusProductStatement F T n := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.fieldT2
  let A := Fin (n + 1) → F.Carrierˣ
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  intro X Y hX hY
  let I := {χ // χ ∈ X} × {χ // χ ∈ Y}
  refine ⟨?_, ?_⟩
  · intro z
    exact (rootCoordinateFiniteFunction F T n).2.2.2 _ _
      (hX _ z.1.property) (hY _ z.2.property)
  · intro φ φ' Φ k
    choose Ψ hΨ using fun z : I =>
      rootSchwartzAssembly F.Carrier n (φ z.1) (φ' z.2) Φ k
    refine ⟨Ψ, ?_⟩
    intro a
    have hcoord := (rootCoordinateChange F T n).2.2.2.2.2.2 a
    simp_rw [hcoord.1, hcoord.2.2.2.1 k, hΨ]
    rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro χ _
    apply Finset.sum_congr rfl
    intro χ' _
    ring

end Langlands.RankinSelberg
