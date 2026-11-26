import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceConstants
import Langlands.Representation.Plancherel.RationalPlancherelConstantCommonLevi
import Langlands.BruhatTits.SpecialCompact.SemistandardParabolicSplitting
import Langlands.GroupScheme.Rational.CocharacterCentralizerPointDetection

/-! # Fixed-Levi independence of the actual source constants: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  (hG : IsConnectedReductive G)
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

/-- **Fixed-Levi independence of the source constants.** At a common compact with the
special-compact properties for a generic positive system of a maximal split torus, the
actual source gamma and the actual constant `c` agree for any two cocharacter
presentations of semistandard indices with the same Levi subgroup functor. -/
theorem sourceConstantParabolicIndependence :
    SourceConstantParabolicIndependenceStatement (i := i) hG := by
  intro hi nu hnu K hK hspec p q r s hpq
  let : Smooth G.X.hom := hG.smooth
  have hlevi : Dynamic.centralizer r.hom = Dynamic.centralizer s.hom :=
    r.levi_eq.trans (hpq.trans s.levi_eq.symm)
  have hz : ∀ α ∈ relativeRoots i,
      latticePairing S α r.cocharacter = 0 ↔ latticePairing S α s.cocharacter = 0 :=
    fun α hα =>
      ⟨root_zero_imp_of_dynamicCentralizer_rationalPoints_le hi.1.1 i r.cocharacter
          s.cocharacter (by rw [hlevi]) hα,
        root_zero_imp_of_dynamicCentralizer_rationalPoints_le hi.1.1 i s.cocharacter
          r.cocharacter (by rw [hlevi]) hα⟩
  have hKs : ∀ (ξ : cocharacterLattice S)
      (x : (Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))),
      (x : rationalPoints G) ∈ K →
        (Dynamic.limitHom (CommGroupScheme.groupHom ξ ≫ i)
          (Over.mk (𝟙 (Spec (CommRingCat.of F)))) x : rationalPoints G) ∈ K := fun ξ =>
    (RationalDynamicSource.compact_split_iff_limit_stable (CommGroupScheme.groupHom ξ ≫ i)
      K).mp fun m u =>
        BruhatTits.SpecialCompact.mul_mem_iff_of_weylRepresentatives hG hi hnu hspec.2.2.1
          hspec.2.2.2 ξ m.2 u.2
  have hgamma : SourceConstants.gamma r K hK = SourceConstants.gamma s K hK :=
    RationalDynamicSource.gamma_eq_of_pairing_zero_iff hG hi K hK hKs _ _ hz
  refine ⟨hgamma, ?_⟩
  change (SourceConstants.gamma r K hK)⁻¹ *
      RationalDynamicSource.rankOneGammaProduct i r.cocharacter K hK =
    (SourceConstants.gamma s K hK)⁻¹ *
      RationalDynamicSource.rankOneGammaProduct i s.cocharacter K hK
  rw [hgamma, RationalDynamicSource.rankOneGammaProduct_eq_of_pairing_zero_iff K hK hG hi hKs hz]

end Langlands.HarishChandraSchwartz.RationalSemistandard
