import Langlands.Representation.Plancherel.DynamicCommonLeviPresentations
import Langlands.Representation.Plancherel.DynamicCommonLeviPointAssembly

/-! # Structural assembly of the closed common-Levi continuation target -/

noncomputable section

set_option maxHeartbeats 400000

universe u uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviContinuation

open DynamicOppositeStandardIntertwining DynamicCommonLeviPresentations

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine

/-- A simultaneous common-Levi presentation together with the represented
auxiliary opposite required by its second split-component direction. -/
def commonLeviAssemblyData
    {F : Type u} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (χ ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hG : IsConnectedReductive G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ) :
    Σ d : CommonData χ ψ ψ',
      OppositeData (CommGroupScheme.groupHom (-d.second.r.splitComponentCocharacter) ≫
        d.a ≫ d.second.l ≫ d.second.p) := by
  let d := commonData χ ψ ψ' hG hψ hψ'
  exact ⟨d, oppositeData hG _⟩

/-- Construct all structural inputs from the data of the exact closed target.
The source analytic theorem and its presentation reduction remain explicit
premises, to be discharged by their independently owned proofs. -/
theorem conditionalDynamicCommonLeviContinuation_of_presentationReduction
    (hReduction : DynamicCommonLeviPresentationReductionStatement.{u, uV, uW})
    (hIV : ConditionalParabolicIntertwiningStatement.{u, uV, uW}) :
    ConditionalDynamicCommonLeviContinuationStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG χ K hK ψ hψ hψK ψ' hψ' hψ'K A hA hAlen
  let c := commonLeviAssemblyData χ ψ ψ' hG hψ hψ'
  let d := c.1
  let o := c.2
  let : LocallyOfFiniteType (parameterScheme χ).X.hom :=
    parameterScheme_locallyOfFiniteType χ
  exact commonLeviContinuationExists_of_presentations hReduction hIV F G hG
    χ ψ ψ' hψ hψ' d.T (parameterScheme χ) d.first.P d.second.P o.Q
    d.first.U d.second.U o.V d.first.p d.first.l d.second.p d.second.l d.a
    d.first.n d.second.n o.q o.v d.first.r d.second.r (d.levi_comp)
    d.first.radical d.second.radical o.represented o.radical
    d.first.realizes d.second.realizes K hK hψK hψ'K A hA hAlen

end Langlands.Plancherel.DynamicCommonLeviContinuation
