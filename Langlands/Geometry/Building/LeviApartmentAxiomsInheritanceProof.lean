import Langlands.Geometry.Building.LeviApartmentAxiomsInheritanceStatement
import Langlands.BruhatTits.SpecialCompact.LeviApartmentAxioms
import Langlands.BruhatTits.SpecialCompact.LeviApartmentComparison
import Langlands.Geometry.Building.NormalizerImageAffineWeylBounds
import Langlands.Geometry.Building.LeviRestrictionCompatibility
import Langlands.Geometry.Building.SpecialCompactLevi
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Proof that the apartment axioms pass to a standard Levi subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Geometry.Building

section Roots

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom] [Smooth G.X.hom] [LocallyOfFiniteType M.X.hom]
    (i : S.toGrp ⟶ G) (iM : S.toGrp ⟶ M)
    (j : M ⟶ G) (hcomp : iM ≫ j = i) (ζ : cocharacterLattice S)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)

include hcomp hj in
/-- A Levi with defining cocharacter `ζ = 0` has the same relative roots as `G`. -/
theorem relativeRoots_levi_eq_of_cocharacter_eq_zero (hζ : ζ = 0) :
    relativeRoots iM = relativeRoots i := by
  rw [relativeRoots_centralizer_factor dynamicLie i iM j hcomp ζ hj, hζ]
  ext α
  simp

end Roots

section DynamicLevi

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [LocallyOfFiniteType M.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (iM : S.toGrp ⟶ M)
    [Mono i.hom.hom.left] [Mono iM.hom.hom.left]
    (j : M ⟶ G) (hcomp : iM ≫ j = i) (ζ : cocharacterLattice S)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : KPApartmentData i (localFieldOrder F))

local notation "DM" => leviRestrictedApartmentData hS i iM j hcomp ζ hj hjc hG hi D

/-- The restriction of an apartment class satisfying V 7 and AS 2–AS 5 to a Levi subgroup `M`
(the centralizer of a cocharacter `ζ` of `S`) satisfies V 7 and AS 2–AS 5, provided it satisfies
V 6 for the centralizer datum `CM` of `S` in `M`. -/
theorem satisfiesApartmentAxioms_leviRestricted (hM : IsConnectedReductive M)
    (hiM : IsMaximalSplitTorus iM) {C : CentralizerDatum i} (CM : CentralizerDatum iM)
    (hD : D.SatisfiesApartmentAxioms C)
    (hV6 : (DM).IsOmegaCompatible CM) : (DM).SatisfiesApartmentAxioms CM := by
  let B : ValuationBuildingData M := ⟨hM, S, iM, hiM, DM, CM, hV6⟩
  have hAS2 := isAffineRootSystem_levi hS i iM j hcomp ζ hj hjc hG hi D
    (mem_extendedAffineRoots_levi_iff hS i iM j hcomp ζ hj hjc hG hi D)
    (fun _ ⟨a, ha, _⟩ => ⟨a, ha⟩) hD.isAffineRootSystem_extendedAffineRoots
    hD.derivativeRoots_extendedAffineRoots
  have hAS3 := isAffineRootSystem_levi hS i iM j hcomp ζ hj hjc hG hi D
    (mem_affineRoots_levi_iff hS i iM j hcomp ζ hj hjc hG hi D)
    (fun _ ⟨a, ha, _⟩ => ⟨a, ha⟩) hD.isAffineRootSystem_affineRoots hD.derivativeRoots_affineRoots
  have hAS4 := mem_or_two_smul_mem_levi hS i iM j hcomp ζ hj hjc hG hi D hD.mem_or_two_smul_mem
  have hlow : AffineRootSystem.affineWeylGroup (DM).affineRoots ≤ (DM).normalizerAffineEquiv.range :=
    B.affineWeylGroup_le_range_of_AS3 hAS3.1
  have hup : (DM).normalizerAffineEquiv.range ≤
      AffineRootSystem.extendedAffineWeylGroup (DM).affineRoots :=
    B.range_le_extendedAffineWeylGroup_of_AS4 hAS4
  have hiMc : IsClosedSubgroup iM := hiM.isSplitSubtorus.2
  refine ⟨hV6, isTopologyCompatible_levi hS i iM j hcomp ζ hj hjc hG hi D hD.topologyCompatible,
    hAS2.1, hAS2.2, hAS3.1, hAS3.2, hAS4, hlow, hup, fun hsc => ?_, fun hqs had => ?_⟩
  · obtain ⟨e, -⟩ := exists_leviIso_of_isSemisimple hS i iM j hcomp ζ hj hiMc hsc.isSemisimple
    have hR := relativeRoots_levi_eq_of_cocharacter_eq_zero i iM j hcomp ζ hj
      (cocharacter_eq_zero_of_isSemisimple_levi hS i iM j hcomp ζ hj hiMc hsc.isSemisimple)
    exact range_eq_affineWeylGroup_levi hS i iM j hcomp ζ hj hjc hG hi D hR
      (hD.range_eq_affineWeylGroup_of_isSimplyConnected (hsc.of_iso e.symm)) hlow
  · obtain ⟨e, -⟩ := exists_leviIso_of_isSemisimple hS i iM j hcomp ζ hj hiMc had.isSemisimple
    have : IsIso j := isIso_leviHom_of_isSemisimple hS i iM j hcomp ζ hj hiMc had.isSemisimple
    have hR := relativeRoots_levi_eq_of_cocharacter_eq_zero i iM j hcomp ζ hj
      (cocharacter_eq_zero_of_isSemisimple_levi hS i iM j hcomp ζ hj hiMc had.isSemisimple)
    exact range_eq_extendedAffineWeylGroup_levi hS i iM j hcomp ζ hj hjc hG hi D hR
      (hD.range_eq_extendedAffineWeylGroup_of_isQuasiSplit_of_isAdjoint (hqs.of_iso e.symm)
        (had.of_iso e.symm)) hup

end DynamicLevi

/-- V 6, V 7 and AS 2–AS 5 pass from an apartment class of `(G, S)` to any apartment class of a
standard Levi subgroup `(M_J, S)` containing the restriction of one of its points (KP §6.7). -/
theorem leviApartmentAxiomsInheritance : LeviApartmentAxiomsInheritanceStatement.{u} := by
  intro F _ _ _ _ G hG S i hi ν hν J hJ C CM D DM hpair hD
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  have hiM := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have : Mono (Standard.leviTorusHom i ν J).hom.hom.left := hiM.isSplitSubtorus.mono
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : Smooth (Standard.leviScheme i ν J).X.hom :=
    (standardLeviSplitComponentStatement F G hG S i hi ν hν J hJ).1.smooth
  have hS : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  obtain ⟨ζ, hζ⟩ :=
    StandardLeviSplitComponent.exists_standardLevi_eq_dynamicCentralizer hG hS i ν J
  have hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
      (Standard.leviHom i ν J) := hζ ▸ Standard.isRepresentedBy_leviHom i ν J
  have hV6 := isOmegaCompatible_standardLevi_of_pair ν J CM hpair hD.omegaCompatible
  obtain rfl := eq_leviRestrictedApartmentData_of_pair hS i (Standard.leviTorusHom i ν J)
    (Standard.leviHom i ν J) (Standard.leviTorusHom_comp i ν J) ζ hj
    (Standard.isClosedSubgroup_leviHom i ν J) hG hi D DM hpair
  exact satisfiesApartmentAxioms_leviRestricted hS i (Standard.leviTorusHom i ν J)
    (Standard.leviHom i ν J) (Standard.leviTorusHom_comp i ν J) ζ hj
    (Standard.isClosedSubgroup_leviHom i ν J) hG hi D
    (standardLevi_isConnectedReductive hG i hi ν hν J hJ) hiM CM hD hV6

end Langlands.Geometry.Building
