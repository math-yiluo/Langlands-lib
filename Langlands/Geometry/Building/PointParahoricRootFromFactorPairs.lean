import Langlands.Geometry.Building.PointParahoricNormalizer
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence

/-! # Point-parahoric root intersections from local opposite factor pairs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- Opposite corrections to a root point of negative valuation lie in the
point parahoric. Their normalizing product would have to fix the point,
contradicting its translation value on the root. -/
theorem mem_filtration_of_mem_rootGroup_of_mem_parahoricAt_of_factorPairs
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hE : RelativeRoot.HasOppositeFactorPairs P.i)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    {g : rationalPoints G} (hgRoot : g ∈ P.rootGroup a)
    (hgP : g ∈ P.parahoricAt x) :
    g ∈ P.filtration x a 0 := by
  have : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hT := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hrank := RelativeRoot.hasRankOneFactorization_of_hasOppositeFactorPairs
    P.i hT hE
  by_cases hg1 : g = 1
  · simpa only [hg1] using (P.filtration x a 0).one_mem
  obtain ⟨t, ht⟩ := KPApartmentData.exists_val_eq_coe x ha hgRoot hg1
  have ht0 : 0 ≤ t := by
    by_contra hnegative
    have htneg : t < 0 := lt_of_not_ge hnegative
    obtain ⟨p, hp⟩ := hE a ha g hgRoot hg1
    have hflip := hp.weylAction_eq_neg P.i hT ha.1 hgRoot hg1
    have hnega : -a ∈ relativeRoots P.i := by
      rw [← hflip]
      exact weylAction_mapsTo_relativeRoots P.i _ ha
    have hp1val := x.isValuation.opposite a ha g hgRoot hg1
      p.1 hp.1 p.2 hp.2.1 hp.2.2
    rw [ht] at hp1val
    have hp1t := withTop_eq_neg_of_add_eq_zero hp1val
    have hp2val := x.isValuation.opposite_snd ha hgRoot hg1 hp.1 hp.2.1 hp.2.2
    rw [ht] at hp2val
    have hp2t := withTop_eq_neg_of_add_eq_zero hp2val
    have hp1F : p.1 ∈ P.filtration x (-a) 0 :=
      ⟨hp.1, by rw [hp1t]; exact WithTop.coe_le_coe.mpr (by linarith)⟩
    have hp2F : p.2 ∈ P.filtration x (-a) 0 :=
      ⟨hp.2.1, by rw [hp2t]; exact WithTop.coe_le_coe.mpr (by linarith)⟩
    have hFP : P.filtration x (-a) 0 ≤ P.parahoricAt x :=
      (P.apartment.filtration_le_sharpFixer x hnega).trans
        (P.sharpFixer_le_parahoric {x})
    let m : normalizerPoints P.i := ⟨p.1 * g * p.2, hp.2.2⟩
    have hmP : (m : rationalPoints G) ∈ P.parahoricAt x :=
      (P.parahoricAt x).mul_mem
        ((P.parahoricAt x).mul_mem (hFP hp1F) hgP) (hFP hp2F)
    have hmx : m • x = x :=
      P.normalizer_smul_eq_self_of_mem_parahoricAt hP hrank x m hmP
    have hw : m • x.val = (0 : V P.S) +ᵥ x.val := by
      simpa only [KPApartmentData.val_smul, zero_vadd] using
        congrArg (fun y : P.Apartment => y.val) hmx
    have heval := KPApartmentData.eval_translation_eq_of_factor
      x ha hnega hgRoot hg1 hp.1 hp.2.1 hp.2.2 hflip ht hw
    rw [map_zero] at heval
    linarith
  exact ⟨hgRoot, by rw [ht]; exact WithTop.coe_le_coe.mpr ht0⟩

/-- The actual root-group intersection is its depth-zero filtration, under
the apartment axioms and pair existence only for the given torus inclusion. -/
theorem rootGroup_inf_parahoricAt_eq_filtration_of_factorPairs
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hE : RelativeRoot.HasOppositeFactorPairs P.i)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i) :
    P.rootGroup a ⊓ P.parahoricAt x = P.filtration x a 0 := by
  apply le_antisymm
  · intro g hg
    exact P.mem_filtration_of_mem_rootGroup_of_mem_parahoricAt_of_factorPairs
      hP hE x ha hg.1 hg.2
  · exact le_inf (P.filtration_le_rootGroup x a 0)
      ((P.apartment.filtration_le_sharpFixer x ha).trans
        (P.sharpFixer_le_parahoric {x}))

/-- The identity on ambient rational points gives the point-intersection
equivalence from local pair existence, without a global product premise. -/
def rootGroupParahoricAtEquivFiltrationOfFactorPairs
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hE : RelativeRoot.HasOppositeFactorPairs P.i)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i) :
    ↥(P.rootGroup a ⊓ P.parahoricAt x) ≃* P.filtration x a 0 :=
  MulEquiv.subgroupCongr
    (P.rootGroup_inf_parahoricAt_eq_filtration_of_factorPairs hP hE x ha)

@[simp]
theorem rootGroupParahoricAtEquivFiltrationOfFactorPairs_apply
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hE : RelativeRoot.HasOppositeFactorPairs P.i)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (g : ↥(P.rootGroup a ⊓ P.parahoricAt x)) :
    (P.rootGroupParahoricAtEquivFiltrationOfFactorPairs hP hE x ha g :
      rationalPoints G) = g := rfl

end Langlands.Geometry.Building.ParahoricBuildingData
