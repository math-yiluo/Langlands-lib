import Langlands.Representation.Plancherel.RenardStandardLeviParahoricData
import Langlands.BruhatTits.SpecialCompact.LeviSpecialPoint

/-! # The restricted standard-Levi data and the original projected special vertex -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits.SpecialCompact

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ParahoricBuildingData G) (ν : cocharacterLattice B.S)
  (hν : IsGenericCocharacter B.i ν) (J : Set (characterLattice B.S))
  (hJ : J ⊆ simpleRelativeRoots B.i ν)

/-- A cocharacter presenting the actual standard Levi as a dynamic centralizer. -/
def standardLeviRestrictionCocharacter : cocharacterLattice B.S :=
  (StandardLeviSplitComponent.exists_standardLevi_eq_dynamicCentralizer
    B.isConnectedReductive B.isMaximalSplitTorus.isSplitSubtorus.1 B.i ν J).choose

theorem standardLeviRestrictionCocharacter_eq :
    standardLevi B.i ν J = Dynamic.centralizer
      (CommGroupScheme.groupHom (standardLeviRestrictionCocharacter B ν J) ≫ B.i) :=
  (StandardLeviSplitComponent.exists_standardLevi_eq_dynamicCentralizer
    B.isConnectedReductive B.isMaximalSplitTorus.isSplitSubtorus.1 B.i ν J).choose_spec

theorem standardLeviRestriction_isRepresentedBy :
    (Dynamic.centralizer
      (CommGroupScheme.groupHom (standardLeviRestrictionCocharacter B ν J) ≫ B.i)).IsRepresentedBy
        (Standard.leviHom B.i ν J) := by
  rw [← standardLeviRestrictionCocharacter_eq]
  exact Standard.isRepresentedBy_leviHom B.i ν J

local instance : IsAffineHom (Standard.leviScheme B.i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom B.i ν J).isAffineHom
local instance : Mono (Standard.leviTorusHom B.i ν J).hom.hom.left :=
  mono_of_isMaximalSplitTorus
    (Standard.isMaximalSplitTorus_leviTorusHom B.i ν J B.isMaximalSplitTorus)
/-- The actual ambient valuation class restricted to the same standard Levi. -/
def standardLeviRestrictedApartment :
    KPApartmentData (Standard.leviTorusHom B.i ν J) (localFieldOrder F) := by
  letI : Smooth G.X.hom := B.isConnectedReductive.smooth
  letI : ConnectedSpace G.X.left := B.isConnectedReductive.connectedSpace
  letI : Smooth (Standard.leviScheme B.i ν J).X.hom :=
    (standardLeviSplitComponentStatement F G B.isConnectedReductive B.S B.i
      B.isMaximalSplitTorus ν hν J hJ).1.smooth
  exact leviRestrictedApartmentData B.isMaximalSplitTorus.isSplitSubtorus.1 B.i
    (Standard.leviTorusHom B.i ν J) (Standard.leviHom B.i ν J)
    (Standard.leviTorusHom_comp B.i ν J) (standardLeviRestrictionCocharacter B ν J)
    (standardLeviRestriction_isRepresentedBy B ν J)
    (Standard.isClosedSubgroup_leviHom B.i ν J) B.isConnectedReductive
    B.isMaximalSplitTorus B.apartment

/-- Projection from the original apartment to its literal standard-Levi restriction. -/
def standardLeviApartmentProjection (x : B.Apartment) :
    (standardLeviRestrictedApartment B ν hν J hJ).Apartment := by
  letI : Smooth G.X.hom := B.isConnectedReductive.smooth
  letI : ConnectedSpace G.X.left := B.isConnectedReductive.connectedSpace
  letI : Smooth (Standard.leviScheme B.i ν J).X.hom :=
    (standardLeviSplitComponentStatement F G B.isConnectedReductive B.S B.i
      B.isMaximalSplitTorus ν hν J hJ).1.smooth
  exact leviApartmentProjection B.isMaximalSplitTorus.isSplitSubtorus.1 B.i
    (Standard.leviTorusHom B.i ν J) (Standard.leviHom B.i ν J)
    (Standard.leviTorusHom_comp B.i ν J) (standardLeviRestrictionCocharacter B ν J)
    (standardLeviRestriction_isRepresentedBy B ν J)
    (Standard.isClosedSubgroup_leviHom B.i ν J) B.isConnectedReductive
    B.isMaximalSplitTorus B.apartment x

theorem isLeviRestriction_standardLeviApartmentProjection (x : B.Apartment) :
    IsLeviRestriction (Standard.leviHom B.i ν J) x
      (standardLeviApartmentProjection B ν hν J hJ x) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := B.isConnectedReductive.connectedSpace
  let : Smooth (Standard.leviScheme B.i ν J).X.hom :=
    (standardLeviSplitComponentStatement F G B.isConnectedReductive B.S B.i
      B.isMaximalSplitTorus ν hν J hJ).1.smooth
  exact isLeviRestriction_leviApartmentProjection B.isMaximalSplitTorus.isSplitSubtorus.1 B.i
    (Standard.leviTorusHom B.i ν J) (Standard.leviHom B.i ν J)
    (Standard.leviTorusHom_comp B.i ν J) (standardLeviRestrictionCocharacter B ν J)
    (standardLeviRestriction_isRepresentedBy B ν J)
    (Standard.isClosedSubgroup_leviHom B.i ν J) B.isConnectedReductive
    B.isMaximalSplitTorus B.apartment x

theorem standardLeviApartmentProjection_surjective :
    Function.Surjective (standardLeviApartmentProjection B ν hν J hJ) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := B.isConnectedReductive.connectedSpace
  let : Smooth (Standard.leviScheme B.i ν J).X.hom :=
    (standardLeviSplitComponentStatement F G B.isConnectedReductive B.S B.i
      B.isMaximalSplitTorus ν hν J hJ).1.smooth
  exact leviApartmentProjection_surjective B.isMaximalSplitTorus.isSplitSubtorus.1 B.i
    (Standard.leviTorusHom B.i ν J) (Standard.leviHom B.i ν J)
    (Standard.leviTorusHom_comp B.i ν J) (standardLeviRestrictionCocharacter B ν J)
    (standardLeviRestriction_isRepresentedBy B ν J)
    (Standard.isClosedSubgroup_leviHom B.i ν J) B.isConnectedReductive
    B.isMaximalSplitTorus B.apartment

theorem standardLeviRestrictedApartment_all_restrictions
    (xM : (standardLeviRestrictedApartment B ν hν J hJ).Apartment) :
    ∃ x : B.Apartment, IsLeviRestriction (Standard.leviHom B.i ν J) x xM := by
  obtain ⟨x, rfl⟩ := standardLeviApartmentProjection_surjective B ν hν J hJ xM
  exact ⟨x, isLeviRestriction_standardLeviApartmentProjection B ν hν J hJ x⟩

/-- Parahoric data for the actual standard Levi on the restricted ambient class. -/
def restrictedStandardLeviParahoricData :
    ParahoricBuildingData (Standard.leviScheme B.i ν J) :=
  standardLeviParahoricData B ν hν J hJ
    (standardLeviRestrictedApartment B ν hν J hJ)
    (standardLeviRestrictedApartment_all_restrictions B ν hν J hJ)

@[simp]
theorem restrictedStandardLeviParahoricData_centralizer :
    (restrictedStandardLeviParahoricData B ν hν J hJ).centralizer =
      standardLeviCentralizerDatum B.i B.centralizer ν J := rfl

@[simp]
theorem restrictedStandardLeviParahoricData_centralizerZero :
    (restrictedStandardLeviParahoricData B ν hν J hJ).centralizerZero =
      B.centralizerZero := rfl

/-- The original projection is a special vertex under ambient AS3 and specialness. -/
def standardLeviSpecialApartmentVertex
    (hder : AffineRootSystem.derivativeRoots B.apartment.affineRoots =
      Set.range (rootForm B.i))
    (x : B.Apartment) (hx : AffineRootSystem.IsSpecialPoint B.apartment.affineRoots x) :
    {xM : (standardLeviRestrictedApartment B ν hν J hJ).Apartment //
      (standardLeviRestrictedApartment B ν hν J hJ).IsSpecialApartmentVertex xM ∧
        IsLeviRestriction (Standard.leviHom B.i ν J) x xM} := by
  letI : Smooth G.X.hom := B.isConnectedReductive.smooth
  letI : ConnectedSpace G.X.left := B.isConnectedReductive.connectedSpace
  letI : Smooth (Standard.leviScheme B.i ν J).X.hom :=
    (standardLeviSplitComponentStatement F G B.isConnectedReductive B.S B.i
      B.isMaximalSplitTorus ν hν J hJ).1.smooth
  exact leviSpecialApartmentVertex B.isMaximalSplitTorus.isSplitSubtorus.1 B.i
    (Standard.leviTorusHom B.i ν J) (Standard.leviHom B.i ν J)
    (Standard.leviTorusHom_comp B.i ν J) (standardLeviRestrictionCocharacter B ν J)
    (standardLeviRestriction_isRepresentedBy B ν J)
    (Standard.isClosedSubgroup_leviHom B.i ν J) B.isConnectedReductive
    B.isMaximalSplitTorus B.apartment hder x hx

@[simp]
theorem standardLeviSpecialApartmentVertex_val
    (hder : AffineRootSystem.derivativeRoots B.apartment.affineRoots =
      Set.range (rootForm B.i))
    (x : B.Apartment) (hx : AffineRootSystem.IsSpecialPoint B.apartment.affineRoots x) :
    (standardLeviSpecialApartmentVertex B ν hν J hJ hder x hx).val =
      standardLeviApartmentProjection B ν hν J hJ x := rfl

end Langlands.Plancherel.RenardCartan
