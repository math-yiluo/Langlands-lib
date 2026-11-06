import Langlands.GroupScheme.FieldCentralizerRepresentabilityProof
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.BruhatTits.Cartan.CentralizerValuationStatement
import Langlands.Geometry.Building.KPCentralizerCompatibility

/-! # Actual centralizer data from the universal valuation comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.BruhatTits

namespace Langlands.Geometry.Building.CentralizerDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {S : CommGroupScheme (Spec (CommRingCat.of F))}

/-- Choose the actual closed all-test centralizer, factor the maximal split
torus through it, and apply the universal character-valuation comparison. -/
def ofValuationComparison
    (hcomparison : Cartan.CentralizerValuationComparisonStatement.{u})
    (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) : CentralizerDatum i :=
  Classical.choice <| by
    obtain ⟨Z, j, hj, hjc⟩ :=
      fieldCentralizerRepresentability F S G hi.1.1.isAffineHom i
    let s := torusCentralizerFactor i hj
    have hs : s ≫ j = i := torusCentralizerFactor_comp i hj
    exact ⟨{
      Z := Z
      j := j
      s := s
      isClosedSubgroup := hjc
      isRepresentedBy := hj
      comp_eq := hs
      bijective := hcomparison F G hG S i hi Z j hjc hj s hs
    }⟩

end Langlands.Geometry.Building.CentralizerDatum
