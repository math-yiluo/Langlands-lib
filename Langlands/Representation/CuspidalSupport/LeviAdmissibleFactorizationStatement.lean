import Langlands.Representation.Induction.BlockFactors

/-! Same-universe finite tensor factorization of admissible irreducible
representations of actual standard p-adic Levis. This is a derived theorem
target, not a proof of factorization. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uW

/-- Every admissible irreducible representation of an actual standard p-adic
Levi is equivalent to the external tensor of admissible irreducible block
representations whose carriers lie in the universe of the given carrier. -/
def PadicLeviAdmissibleFactorizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ σ : SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier),
      σ.IsIrreducible → σ.IsAdmissible →
      ∃ A : ∀ i : Fin B.length,
        SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F.Carrier),
        (∀ i, (A i).IsIrreducible) ∧ (∀ i, (A i).IsAdmissible) ∧
        Nonempty (σ.representation.Equiv
          (B.blockTensor (fun i => (A i).representation)))

end Langlands.CuspidalSupport
