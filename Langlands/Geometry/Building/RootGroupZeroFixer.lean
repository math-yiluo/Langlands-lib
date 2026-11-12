import Langlands.Geometry.Building.PointParahoricRootIntersection
import Langlands.Geometry.Building.KPParahoricFixerComparison
import Langlands.Geometry.Building.ApartmentRootCover
import Langlands.Geometry.Building.ParahoricBuildingAxioms
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof

/-! # Root groups meet the zero fixers in the root fixers (KP Axiom 4.1.8 (3)) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- `P_Ω ⊆ G(F)^0_Ω`: the parahoric of `Ω` lies in `G(F)^0` and fixes the image of `Ω`. -/
theorem parahoric_le_zeroFixer (hP : P.SatisfiesApartmentAxioms) (Ω : Set P.Apartment) :
    P.parahoric Ω ≤ P.zeroFixer Ω := by
  intro g hg
  refine P.mem_zeroFixer.2 ⟨P.parahoric_le_zeroSubgroup hP Ω hg, fun x hx => ?_⟩
  exact (P.apartment.mem_compactStabilizer.1
    (P.parahoric_le_compactStabilizer hP.topologyCompatible hx hg)).2

/-- The generators of KP Axiom 4.1.8 (2) fix the image of `Ω` and lie in `G(F)^0`. -/
theorem nonnegativeRootSubgroup_le_zeroFixer (hP : P.SatisfiesApartmentAxioms)
    (Ω : Set P.Apartment) : P.nonnegativeRootSubgroup Ω ≤ P.zeroFixer Ω :=
  (P.nonnegativeRootSubgroup_le_parahoric Ω).trans (P.parahoric_le_zeroFixer hP Ω)

/-- An element of the positive unipotent group of a generic cocharacter that fixes the image of
`x` in `B(G)` lies in the positive chamber root groups at `x`. This is
`mem_positiveRootGroups_of_mem_unipotent_of_mem_parahoric` with the point parahoric replaced by
the full point stabilizer `G(F)^♯_x · N(F)_x`. -/
theorem mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (x : P.Apartment) (ν : cocharacterLattice P.S)
    (hν : IsGenericCocharacter P.i ν)
    {g : rationalPoints G}
    (hgU : g ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)))
    (hgx : g • P.apartmentMap x = P.apartmentMap x) :
    g ∈ ⨆ b : positiveRelativeRoots P.i ν, P.apartment.chamberRootGroup x false b := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hνneg : IsGenericCocharacter P.i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  have hsharp := P.toValuationBuildingData.sharpFixer_subset_mul_sharpNormalizerStabilizer
    hP hrank x (-ν) hνneg
  rw [neg_neg] at hsharp
  obtain ⟨m, -, s, hs, hgsm⟩ :=
    (ApartmentQuotient.mem_stabilizer_apartment_iff P.apartment.sharpFixerFamily x g).1
      (MulAction.mem_stabilizer_iff.2 hgx)
  obtain ⟨vw, ⟨v, hv, w, hw, rfl⟩, n, hn, hvwn⟩ := hsharp hs
  change v * w * n = s at hvwn
  have hnN : n ∈ normalizerPoints P.i :=
    (KPApartmentData.mem_sharpNormalizerStabilizer.mp hn).2.1
  let n' : normalizerPoints P.i := ⟨n * m, (normalizerPoints P.i).mul_mem hnN m.property⟩
  have hfactor : v * w * (n' : rationalPoints G) = g := by
    change v * w * (n * m) = g
    rw [← mul_assoc, hvwn, hgsm]
  have hvU := (P.apartment.positiveChamberRootGroups_le_sharpUnipotentPoints x ν hv).1
  have hwU := (P.apartment.positiveChamberRootGroups_le_sharpUnipotentPoints x (-ν) hw).1
  have hpos : v⁻¹ * g ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hvU) hgU
  have hopp : w⁻¹ ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom ν ≫ P.i))).carrier (Over.mk (𝟙 _)) := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter P.i ν]
    exact Subgroup.inv_mem _ hwU
  have heq : (n' : rationalPoints G) = w⁻¹ * (v⁻¹ * g) := by
    rw [← hfactor]
    group
  have hn' : n' = 1 :=
    normalizer_eq_one_of_unipotent_product P.i ν n' ⟨_, hopp⟩ ⟨_, hpos⟩ heq
  have hfactor' : v * w = g := by simpa only [hn', OneMemClass.coe_one, mul_one] using hfactor
  have hwpos : w ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)) := by
    have hwg : w = v⁻¹ * g := by rw [← hfactor']; group
    rw [hwg]
    exact hpos
  have hwopp : w ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom ν ≫ P.i))).carrier (Over.mk (𝟙 _)) := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter P.i ν]
    exact hwU
  have hw1 : w = 1 :=
    Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic
      (CommGroupScheme.groupHom ν ≫ P.i) hwopp
      (Dynamic.unipotent_le_parabolic _ _ hwpos)
  have hvg : v = g := by simpa only [hw1, mul_one] using hfactor'
  exact hvg ▸ hv

/-- KP Lemma 7.7.3 for the full point stabilizer: an element of `U_a(F)` fixing the image of `x`
in `B(G)` lies in `U_{a,x,0}`. -/
theorem mem_filtration_of_mem_rootGroup_of_smul_apartmentMap_eq
    (hP : P.SatisfiesApartmentAxioms)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    {g : rationalPoints G} (hgRoot : g ∈ P.rootGroup a)
    (hgx : g • P.apartmentMap x = P.apartmentMap x) :
    g ∈ P.filtration x a 0 := by
  have : Smooth G.X.hom := P.isConnectedReductive.smooth
  obtain ⟨ν₀, hν₀⟩ :=
    P.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter P.i
  have hchoice : ∃ ν : cocharacterLattice P.S,
      IsGenericCocharacter P.i ν ∧ 0 < latticePairing P.S a ν := by
    rcases lt_or_gt_of_ne (hν₀ a ha) with hneg | hpos
    · refine ⟨-ν₀, ?_, ?_⟩
      · intro b hb
        simpa only [map_neg] using neg_ne_zero.mpr (hν₀ b hb)
      · simpa only [map_neg] using neg_pos.mpr hneg
    · exact ⟨ν₀, hν₀, hpos⟩
  obtain ⟨ν, hν, hpos⟩ := hchoice
  have hgU := RelativeRoot.subgroup_le_dynamicUnipotent P.i ν hpos
    (Over.mk (𝟙 _)) hgRoot
  exact P.apartment.mem_filtration_of_mem_rootGroup_of_mem_positiveRootGroups
    RelativeRoot.dynamicRootOrderedProduct P.isConnectedReductive P.isMaximalSplitTorus
    hP.isAffineRootSystem_extendedAffineRoots hP.derivativeRoots_extendedAffineRoots
    x ν ⟨ha, hpos⟩ hgRoot
    (P.mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq hP
      (rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
      x ν hν hgU hgx)

/-- `U_a(F) ∩ G(F)^0_Ω = U_{a,Ω,0}` for every `Ω ⊆ A` and every relative root `a`. -/
theorem rootGroup_inf_zeroFixer_eq_rootFixer (hP : P.SatisfiesApartmentAxioms)
    (Ω : Set P.Apartment) (α : relativeRoots P.i) :
    P.rootGroup α ⊓ P.zeroFixer Ω = P.rootFixer α Ω := by
  apply le_antisymm
  · rintro g ⟨hgRoot, hgΩ⟩
    have hfix := (P.mem_zeroFixer.1 hgΩ).2
    exact P.apartment.mem_rootFixer.2 ⟨hgRoot, fun x hx =>
      P.mem_filtration_of_mem_rootGroup_of_smul_apartmentMap_eq hP x α.2 hgRoot (hfix x hx)⟩
  · exact le_inf inf_le_left
      ((P.rootFixer_le_parahoric α Ω).trans (P.parahoric_le_zeroFixer hP Ω))

/-- KP Axiom 4.1.8 (3) for the building of `P`. -/
theorem hasRootZeroFixers (hP : P.SatisfiesApartmentAxioms) : P.HasRootZeroFixers :=
  fun Ω _ _ α => P.rootGroup_inf_zeroFixer_eq_rootFixer hP Ω α

end ParahoricBuildingData

/-- KP Axiom 4.1.8 (3) for the building of KP Chapter 7, on supplied data over a nonarchimedean
local field: under V 7 and AS 2–AS 5 for the class `A(S)` of `P`, for every non-empty bounded
`Ω ⊆ A(S)` and every relative root `a`, `U_a(F) ∩ G(F)^0_Ω = U_{a,Ω,0}`. In KP this is
Lemma 7.7.3 (KP 4.1.28). -/
def RootZeroFixersStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G),
    P.SatisfiesApartmentAxioms → P.HasRootZeroFixers

/-- Proof of `RootZeroFixersStatement`: part (3) of the target of KP Axiom 4.1.8. -/
theorem rootZeroFixers : RootZeroFixersStatement.{u} :=
  fun _ _ _ _ _ _ _ P hP => P.hasRootZeroFixers hP

end Langlands.Geometry.Building
