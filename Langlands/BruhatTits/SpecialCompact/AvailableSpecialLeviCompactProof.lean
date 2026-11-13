import Langlands.BruhatTits.SpecialCompact.AvailableSpecialLeviCompactStatement
import Langlands.BruhatTits.SpecialCompact.ValidTorusRebasingProof
import Langlands.BruhatTits.SpecialCompact.PrescribedLeviSpecialVertex
import Langlands.BruhatTits.SpecialCompact.StandardLeviCompactInclusion
import Langlands.BruhatTits.Iwasawa.AvailableProof

/-! # Available data for the Levi part of a special compact subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.BruhatTits.SpecialCompact

section Witness

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ParahoricBuildingData G) (hB : B.SatisfiesPartialBuildingAxioms)
    (ν : cocharacterLattice B.S) (hν : IsGenericCocharacter B.i ν)
    (J : Set (characterLattice B.S)) (hJ : J ⊆ simpleRelativeRoots B.i ν)
    (x : B.Apartment) (hx : B.apartment.IsSpecialApartmentVertex x)
    (hK : IsCompactOpenMaximal F (B.apartment.specialCompactSubgroup x))

local instance : IsAffineHom (Standard.leviScheme B.i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom B.i ν J).isAffineHom

variable {SM : CommGroupScheme (Spec (CommRingCat.of F))}
    (iM : SM.toGrp ⟶ Standard.leviScheme B.i ν J) [Mono iM.hom.hom.left]
    (CM : CentralizerDatum iM) (DM : KPApartmentData iM (localFieldOrder F))
    (hDM : DM.IsOmegaCompatible CM) (hDMtop : DM.IsTopologyCompatible)
    (hSM : SM = B.S) (hiM : HEq iM (Standard.leviTorusHom B.i ν J))
    (hmax : ∀ (νM : cocharacterLattice SM), IsGenericCocharacter iM νM →
      ∀ xM : DM.Apartment, DM.IsSpecialApartmentVertex xM →
        IsCompactOpenMaximal F (DM.specialCompactSubgroup xM))

include hB hν hJ hx hK hDM hDMtop hSM hiM hmax in
private theorem exists_specialCompactLevi_witness :
    ∃ xM : DM.Apartment, DM.IsSpecialApartmentVertex xM ∧
      DM.specialCompactSubgroup xM = B.apartment.specialCompactLeviSubgroup ν J x := by
  subst SM
  have hiM' : iM = Standard.leviTorusHom B.i ν J := eq_of_heq hiM
  subst iM
  obtain ⟨xM, hxMs, hxM⟩ := prescribedLeviSpecialVertex
    B.isConnectedReductive B.i B.isMaximalSplitTorus B.centralizer B.apartment
    B.isOmegaCompatible hB.apartmentAxioms.derivativeRoots_affineRoots
    ν hν J hJ CM DM hDM x hx.1
  have hνM : IsGenericCocharacter (Standard.leviTorusHom B.i ν J) ν := by
    intro a ha
    exact hν a (relativeRoots_subset_of_factor (Standard.isRepresentedBy_leviHom B.i ν J)
      (Standard.leviTorusHom B.i ν J) (Standard.leviTorusHom_comp B.i ν J) ha)
  have hmaxM := hmax ν hνM xM hxMs
  have hle := standardLeviSpecialCompactSubgroup_le
    B.isConnectedReductive B.i B.isMaximalSplitTorus B.centralizer B.apartment
    B.isOmegaCompatible ν hν J hJ CM DM hDM hDMtop x xM hxM
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsAffine (Standard.leviScheme B.i ν J).X.left :=
    isAffine_of_isAffineHom (Standard.leviScheme B.i ν J).X.hom
  let : TopologicalSpace (rationalPoints (Standard.leviScheme B.i ν J)) :=
    rationalPointTopology F (Standard.leviScheme B.i ν J).X
  have hcompact :
      IsCompact (B.apartment.specialCompactLeviSubgroup ν J x :
        Set (rationalPoints (Standard.leviScheme B.i ν J))) :=
    RenardCartan.isCompact_specialCompactLeviSubgroup B ν J x hK.1
  exact ⟨xM, hxMs, le_antisymm hle (hmaxM.2.2.2 hcompact hle)⟩

end Witness

/-- The Levi part of a special compact subgroup is special compact for available Levi data. -/
theorem availableSpecialLeviCompact : AvailableSpecialLeviCompactStatement.{u} := by
  intro F _ _ _ _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  intro 𝔅 h𝔅
  dsimp only
  intro ν hν x hx J hJ
  let B := (𝔅.datum F G hG).base
  have havail := h𝔅.isAvailableFor (F := F) (G := G) (hG := hG)
  have hM := standardLevi_isConnectedReductive hG B.i B.isMaximalSplitTorus ν hν J hJ
  let : IsAffineHom (Standard.leviScheme B.i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom B.i ν J).isAffineHom
  obtain ⟨𝔅M, h𝔅M, hSM, hiM⟩ :=
    validAssignmentTorusRebasing 𝔅 h𝔅 F (Standard.leviScheme B.i ν J) hM B.S
      (Standard.leviTorusHom B.i ν J)
      (Standard.isMaximalSplitTorus_leviTorusHom B.i ν J B.isMaximalSplitTorus)
  have havailM := h𝔅M.isAvailableFor
    (F := F) (G := Standard.leviScheme B.i ν J) (hG := hM)
  refine ⟨hM, 𝔅M, havailM, hSM, hiM, ?_⟩
  have hK : IsCompactOpenMaximal F (B.apartment.specialCompactSubgroup x) :=
    ((Iwasawa.availableIwasawa F G hG 𝔅 havail ν hν).1 x hx).2.2.2
  let BM := (𝔅M.datum F (Standard.leviScheme B.i ν J) hM).base
  have hmaxM : ∀ (νM : cocharacterLattice BM.S), IsGenericCocharacter BM.i νM →
      ∀ y : BM.Apartment, BM.apartment.IsSpecialApartmentVertex y →
        IsCompactOpenMaximal F (BM.apartment.specialCompactSubgroup y) := by
    intro νM hνM y hy
    exact ((Iwasawa.availableIwasawa F (Standard.leviScheme B.i ν J) hM
      𝔅M havailM νM hνM).1 y hy).2.2.2
  exact exists_specialCompactLevi_witness B
    havail.satisfiesPartialBuildingAxioms ν hν J hJ x hx hK BM.i BM.centralizer
    BM.apartment BM.isOmegaCompatible
    havailM.groupAxioms.affineRootSystem.apartmentAxioms.topologyCompatible hSM hiM hmaxM

end Langlands.BruhatTits.SpecialCompact
