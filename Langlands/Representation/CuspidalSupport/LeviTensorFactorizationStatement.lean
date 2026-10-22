import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Induction.BlockFactors

/-! Small-carrier tensor exhaustion for irreducible cuspidal standard Levis.
This is a derived theorem target, not a proof of factorization or shrinking. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uW uV

/-- Every irreducible cuspidal representation of an actual standard p-adic
Levi is equivalent to the external tensor of irreducible supercuspidal block
representations, whose carriers lie in an independently prescribed universe. -/
def PadicLeviCuspidalFactorizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.topology
    ∀ σ : SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier),
      σ.IsIrreducible → IsLeviCuspidal B σ.representation →
      ∃ A : ∀ i : Fin B.length,
        SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i),
        Nonempty (σ.representation.Equiv
          (B.blockTensor (fun i => (A i).obj.representation)))

end Langlands.CuspidalSupport
