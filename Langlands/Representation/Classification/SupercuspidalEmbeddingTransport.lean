import Langlands.Representation.Classification.SupercuspidalSupportStatement
import Langlands.Representation.Induction.Equivalences

/-! Internal transport and packaging helpers for the supercuspidal embedding proof. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ}

/-- Actual supercuspidal factors of a block shape determine cuspidal data whose
product realizes every irreducible representation embedded into that product. -/
theorem exists_cuspidalSubrepresentation_of_product_embedding
    (B : GeneralLinear.BlockShape n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology
      π.IsIrreducible)
    (j : letI := T.topology
      π.representation.IntertwiningMap
        (T.normalizedProductInduced B (fun i => (A i).obj.representation)))
    (hj : Function.Injective j) :
    ∃ (k : ℕ) (ρ : Fin k → CuspidalDatum.{uV, uF} T), T.IsCuspidalSubrepresentation ρ π := by
  let := T.topology
  let ρ : Fin B.length → CuspidalDatum.{uV, uF} T := fun i =>
    { rank := B.size i
      rank_pos := B.positive i
      cls := (A i).isoClass }
  exact ⟨B.length, ρ, B.sum_eq, A, fun _ => rfl, hπ, j, hj⟩

/-- A Levi embedding and an actual equivalence with supercuspidal block factors
produce the published support relation. This helper does not assert the existence
of either input. -/
theorem exists_cuspidalSubrepresentation_of_levi_equiv
    (B : GeneralLinear.BlockShape n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
    {V : Type uW} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (e : letI := T.topology
      σ.Equiv (B.blockTensor (fun i => (A i).obj.representation)))
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology
      π.IsIrreducible)
    (j : letI := T.topology
      π.representation.IntertwiningMap (T.normalizedParabolicInduced B σ))
    (hj : Function.Injective j) :
    ∃ (k : ℕ) (ρ : Fin k → CuspidalDatum.{uV, uF} T), T.IsCuspidalSubrepresentation ρ π := by
  let := T.topology
  let eInd := T.normalizedParabolicInducedEquiv B e
  exact T.exists_cuspidalSubrepresentation_of_product_embedding B A π hπ
    (eInd.toIntertwiningMap.comp j) (eInd.injective.comp hj)

end Langlands.PadicField.TopologicalData
