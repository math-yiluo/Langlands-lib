import Langlands.BruhatTits.SpecialCompact.LeviApartmentComparison
import Langlands.BruhatTits.SpecialCompact.LeviSpecialPoint

/-! # A special vertex in a prescribed compatible standard-Levi apartment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.Plancherel

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] (hi : IsMaximalSplitTorus i)
    (C : CentralizerDatum i) (D : KPApartmentData i (localFieldOrder F))
    (hD : D.IsOmegaCompatible C)
    (hder : AffineRootSystem.derivativeRoots D.affineRoots = Set.range (rootForm i))
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ν)

local instance prescribedLeviSpecialVertexAffineHom : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom

variable [Mono (Standard.leviTorusHom i ν J).hom.hom.left]
    (CM : CentralizerDatum (Standard.leviTorusHom i ν J))
    (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F))
    (hDM : DM.IsOmegaCompatible CM)

/-- Project an ambient special point to a special vertex of any prescribed
full omega-compatible standard-Levi class, with literal valuation restriction. -/
def prescribedLeviSpecialVertex (x : D.Apartment)
    (hx : AffineRootSystem.IsSpecialPoint D.affineRoots x) :
    {xM : DM.Apartment // DM.IsSpecialApartmentVertex xM ∧
      IsLeviRestriction (Standard.leviHom i ν J) x xM} := by
  apply Classical.choice
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  have hM := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  let : Smooth (Standard.leviScheme i ν J).X.hom := hM.smooth
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  have hj := Standard.isRepresentedBy_leviHom i ν J
  rw [(hcompare ζ hζ).2.1] at hj
  let R := leviRestrictedApartmentData hi.isSplitSubtorus.1 i
    (Standard.leviTorusHom i ν J) (Standard.leviHom i ν J)
    (Standard.leviTorusHom_comp i ν J) ζ hj
    (Standard.isClosedSubgroup_leviHom i ν J) hG hi D
  have hres : ∀ yM : R.Apartment, ∃ y : D.Apartment,
      IsLeviRestriction (Standard.leviHom i ν J) y yM := by
    intro yM
    obtain ⟨y, rfl⟩ := leviApartmentProjection_surjective hi.isSplitSubtorus.1 i
      (Standard.leviTorusHom i ν J) (Standard.leviHom i ν J)
      (Standard.leviTorusHom_comp i ν J) ζ hj
      (Standard.isClosedSubgroup_leviHom i ν J) hG hi D yM
    exact ⟨y, isLeviRestriction_leviApartmentProjection hi.isSplitSubtorus.1 i
      (Standard.leviTorusHom i ν J) (Standard.leviHom i ν J)
      (Standard.leviTorusHom_comp i ν J) ζ hj
      (Standard.isClosedSubgroup_leviHom i ν J) hG hi D y⟩
  let CR := RenardCartan.standardLeviCentralizerDatum i C ν J
  have hRω : R.IsOmegaCompatible CR :=
    RenardCartan.isOmegaCompatible_standardLevi_of_restriction i C ν J D R hD hres
  have hDMω : DM.IsOmegaCompatible CR := hDM.of_centralizerDatum CR
  have hEq : R = DM :=
    omegaCompatibleApartmentUniqueness F (Standard.leviScheme i ν J) hM S
      (Standard.leviTorusHom i ν J)
      (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi) CR R DM hRω hDMω
  subst DM
  exact ⟨leviSpecialApartmentVertex hi.isSplitSubtorus.1 i
    (Standard.leviTorusHom i ν J) (Standard.leviHom i ν J)
    (Standard.leviTorusHom_comp i ν J) ζ hj
    (Standard.isClosedSubgroup_leviHom i ν J) hG hi D hder x hx⟩

end Langlands.BruhatTits.SpecialCompact
