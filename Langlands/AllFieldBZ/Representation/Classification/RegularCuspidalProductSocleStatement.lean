import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Classification.CanonicalConstituents

/-! The actual socle of normalized induction of distinct supercuspidal factors. -/

namespace Langlands.AllFieldBZ.Classification

open Langlands.GeneralLinear LocalFieldPackage.TopologicalData

universe uF uV

/-- The ordered normalized product of distinct supercuspidal factors has
a single irreducible socle, with equality of the subrepresentation images. -/
def RegularCuspidalProductSocleStatement (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n)
    (A : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i)),
    Function.Injective
      (fun i => (⟨B.size i, B.positive i, (A i).isoClass⟩ : CuspidalDatum.{uV, uF} T)) →
    Langlands.Classification.HasIrreducibleSocle
      ((T.normalizedProductInductionFunctor B).obj fun i => (A i).obj).representation

end Langlands.AllFieldBZ.Classification
