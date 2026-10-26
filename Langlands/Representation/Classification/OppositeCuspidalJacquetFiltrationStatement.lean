import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.CuspidalSupport.JacquetInductionStatement

/-! Transfer of the actual upper associated Jacquet filtration to the opposite radical. -/

namespace Langlands

open CuspidalSupport

universe uF uV

/-- The upper associated-filtration theorem supplies an actual opposite
Jacquet filtration, indexed by the original minimal whole-Levi conjugating
permutations, with their actual transported representations as quotients. -/
def GLOppositeCuspidalJacquetFiltrationFromUpperStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ),
    AssociatedJacquetFiltrationTheorem.{uF, uV} F T n →
    letI := T.topology
    ∀ (B C : GeneralLinear.BlockShape n)
      (ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      IsLeviQuasicuspidal B ρ.representation →
      LevisAssociated (F := F.Carrier) B C →
        let Jo := CuspidalJacquetMultiplicity.oppositeJacquet T C
          (CuspidalJacquetMultiplicity.induced T B (Rep.of ρ.representation))
        ∃ (r : ℕ)
          (e : Fin r ≃ MinimalConjugatingPermutations (F := F.Carrier) B C)
          (s : ObjectRepFiltration Jo r),
          ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
            (transport B C (e i).val.val (e i).property ρ.representation))

end Langlands
