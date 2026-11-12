import Langlands.BruhatTits.SpecialCompact.ApartmentCompactTransport
import Langlands.BruhatTits.SpecialCompact.LeviCompactAlgebraicInclusion
import Langlands.BruhatTits.SpecialCompact.PrescribedLeviSpecialVertex
import Langlands.BruhatTits.SpecialCompact.ParabolicCompactFactorization

/-! # Compact properties and literal Levi inheritance in a compatible apartment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.BruhatTits.SpecialCompact

section StandardInclusion

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] (hi : IsMaximalSplitTorus i)
    (C : CentralizerDatum i) (D : KPApartmentData i (localFieldOrder F))
    (hD : D.IsOmegaCompatible C)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ν)

local instance compatiblePropertiesLeviAffine :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom

variable [Mono (Standard.leviTorusHom i ν J).hom.hom.left]
    (CM : CentralizerDatum (Standard.leviTorusHom i ν J))
    (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F))
    (hDM : DM.IsOmegaCompatible CM)

include hG hi hD hν hJ hDM in
/-- Literal compatible standard-Levi restriction gives the actual compact
inclusion without a separate topology-compatibility premise on the Levi. -/
theorem standardLeviSpecialCompactSubgroup_le_of_compatible
    (x : D.Apartment) (xM : DM.Apartment)
    (hres : IsLeviRestriction (Standard.leviHom i ν J) x xM) :
    DM.specialCompactSubgroup xM ≤ D.specialCompactLeviSubgroup ν J x := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  have hM := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  let : Smooth (Standard.leviScheme i ν J).X.hom := hM.smooth
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  have hj := Standard.isRepresentedBy_leviHom i ν J
  rw [(hcompare ζ hζ).2.1] at hj
  let CR := RenardCartan.standardLeviCentralizerDatum i C ν J
  have hDMR : DM.IsOmegaCompatible CR := hDM.of_centralizerDatum CR
  have hc : CR.j ≫ Standard.leviHom i ν J = (𝟙 C.Z) ≫ C.j := by
    change RenardCartan.standardLeviCentralizerFactor i ν J C.j C.isRepresentedBy ≫
      Standard.leviHom i ν J = (𝟙 C.Z) ≫ C.j
    simpa only [Category.id_comp] using
      (RenardCartan.standardLeviCentralizerFactor_comp i ν J C.j C.isRepresentedBy)
  exact leviSpecialCompactSubgroup_le_comap_of_compatible
    (hS := hi.isSplitSubtorus.1) (i := i) (iM := Standard.leviTorusHom i ν J)
    (j := Standard.leviHom i ν J) (hcomp := Standard.leviTorusHom_comp i ν J)
    (zeta := ζ) (hj := hj) (hjc := Standard.isClosedSubgroup_leviHom i ν J)
    (D := D) (hM := hM)
    (hiM := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi)
    (CM := CR) (C := C) (hD := hD) (c := 𝟙 C.Z) (hc := hc)
    DM hDMR x xM hres

end StandardInclusion

section CompactPreimage

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
    (D : KPApartmentData i (localFieldOrder F))
    (ν : cocharacterLattice S) (J : Set (characterLattice S))

local instance compatiblePropertiesAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance compatiblePropertiesAmbientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- Compactness of the literal Levi preimage, for the original apartment
subgroup and the actual closed standard-Levi inclusion. -/
theorem isCompact_specialCompactLeviSubgroup_of_isCompact
    (x : D.Apartment)
    (hK : IsCompact (D.specialCompactSubgroup x : Set (rationalPoints G))) :
    letI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
      (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
    letI : IsAffine (Standard.leviScheme i ν J).X.left :=
      isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
    letI : TopologicalSpace (rationalPoints (Standard.leviScheme i ν J)) :=
      rationalPointTopology F (Standard.leviScheme i ν J).X
    IsCompact (D.specialCompactLeviSubgroup ν J x :
      Set (rationalPoints (Standard.leviScheme i ν J))) := by
  let : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  let : IsAffine (Standard.leviScheme i ν J).X.left :=
    isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
  let : TopologicalSpace (rationalPoints (Standard.leviScheme i ν J)) :=
    rationalPointTopology F (Standard.leviScheme i ν J).X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let : IsClosedImmersion (Standard.leviHom i ν J).hom.hom.left :=
    Standard.isClosedSubgroup_leviHom i ν J
  exact (isClosedEmbedding_rationalPointMap F
    (Standard.leviHom i ν J).hom.hom).isCompact_preimage hK

end CompactPreimage

section Available

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) (B : KPBuildingAssignment.{u}) (hB : B.IsValid)
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] (hi : IsMaximalSplitTorus i)
    (C : CentralizerDatum i) (D : KPApartmentData i (localFieldOrder F))
    (hD : D.IsOmegaCompatible C)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)

section Witness

variable (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ν)

local instance compatibleWitnessLeviAffine :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
variable [Mono (Standard.leviTorusHom i ν J).hom.hom.left]

/-- Choose a literal restricted compatible Levi apartment and its special
vertex, with maximal compact subgroup equal to the original compact preimage. -/
def compatibleStandardLeviCompact (x : D.Apartment)
    (hx : D.IsSpecialApartmentVertex x) :
    Σ DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F),
      {xM : DM.Apartment //
        DM.IsOmegaCompatible (RenardCartan.standardLeviCentralizerDatum i C ν J) ∧
        DM.IsSpecialApartmentVertex xM ∧
        IsLeviRestriction (Standard.leviHom i ν J) x xM ∧
        IsCompactOpenMaximal F (DM.specialCompactSubgroup xM) ∧
        DM.specialCompactSubgroup xM = D.specialCompactLeviSubgroup ν J x} := by
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
  have hR : R.IsOmegaCompatible CR :=
    RenardCartan.isOmegaCompatible_standardLevi_of_restriction i C ν J D R hD hres
  have hder := availableDerivativeRoots_of_omegaCompatibleApartment hG B hB i hi C D hD
  let yM := leviSpecialApartmentVertex hi.isSplitSubtorus.1 i
    (Standard.leviTorusHom i ν J) (Standard.leviHom i ν J)
    (Standard.leviTorusHom_comp i ν J) ζ hj
    (Standard.isClosedSubgroup_leviHom i ν J) hG hi D hder x hx.1
  have hcore := availableCompactCore_of_omegaCompatibleApartment hG B hB i hi C D hD x hx
  have hcoreM := availableCompactCore_of_omegaCompatibleApartment hM B hB
    (Standard.leviTorusHom i ν J)
    (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi) CR R hR yM.val yM.property.1
  have hle := standardLeviSpecialCompactSubgroup_le_of_compatible hG i hi C D hD
    ν hν J hJ CR R hR x yM.val yM.property.2
  let : IsAffine (Standard.leviScheme i ν J).X.left :=
    isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
  let : TopologicalSpace (rationalPoints (Standard.leviScheme i ν J)) :=
    rationalPointTopology F (Standard.leviScheme i ν J).X
  have heq : R.specialCompactSubgroup yM.val = D.specialCompactLeviSubgroup ν J x :=
    le_antisymm hle (hcoreM.2.1.2.2.2
      (isCompact_specialCompactLeviSubgroup_of_isCompact D ν J x hcore.2.1.1) hle)
  exact ⟨⟨R, yM.val, hR, yM.property.1, yM.property.2, hcoreM.2.1, heq⟩⟩

end Witness

include hG hB hi hD hν in
/-- Actual compact maximality in each restricted Levi forces the literal
standard-parabolic factorization of the original norm-one fixer. -/
theorem availableParabolicFactorization_of_omegaCompatibleApartment
    (x : D.Apartment) (hx : D.IsSpecialApartmentVertex x) :
    HasParabolicFactorization i ν (D.specialCompactSubgroup x) := by
  have hcore := availableCompactCore_of_omegaCompatibleApartment hG B hB i hi C D hD x hx
  apply hasParabolicFactorization_of_maximal_compact_levis hG i hi ν hν
    (D.specialCompactSubgroup x) hcore.2.1.1
  intro J hJ
  let : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  let : Mono (Standard.leviTorusHom i ν J).hom.hom.left :=
    (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi).isSplitSubtorus.mono
  let W := compatibleStandardLeviCompact hG B hB i hi C D hD ν hν J hJ x hx
  change IsCompactOpenMaximal F (D.specialCompactLeviSubgroup ν J x)
  rw [← W.2.property.2.2.2.2]
  exact W.2.property.2.2.2.1

include hG hB hi hD hν in
/-- All four compact properties hold in the prescribed compatible
apartment, for the same original subgroup and generic cocharacter. -/
theorem availableSpecialCompactProperties_of_omegaCompatibleApartment
    (x : D.Apartment) (hx : D.IsSpecialApartmentVertex x) :
    SpecialCompactProperties F i ν (D.specialCompactSubgroup x) := by
  have hcore := availableCompactCore_of_omegaCompatibleApartment hG B hB i hi C D hD x hx
  exact ⟨hcore.1, hcore.2.1, hcore.2.2,
    availableParabolicFactorization_of_omegaCompatibleApartment hG B hB
      i hi C D hD ν hν x hx⟩

section Inheritance

variable (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ν)

local instance compatibleInheritanceLeviAffine :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
variable [Mono (Standard.leviTorusHom i ν J).hom.hom.left]

/-- Package the same actual restricted Levi point with its full compact
properties and exact original compact-preimage equality. -/
def compatibleSpecialLeviRestriction (x : D.Apartment)
    (hx : D.IsSpecialApartmentVertex x) :
    Σ DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F),
      {xM : DM.Apartment // SpecialLeviRestriction F ν D x J DM xM} := by
  let W := compatibleStandardLeviCompact hG B hB i hi C D hD ν hν J hJ x hx
  have hM := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  have hνM : IsGenericCocharacter (Standard.leviTorusHom i ν J) ν := by
    intro a ha
    exact hν a (relativeRoots_subset_of_factor (Standard.isRepresentedBy_leviHom i ν J)
      (Standard.leviTorusHom i ν J) (Standard.leviTorusHom_comp i ν J) ha)
  exact ⟨W.1, W.2.val, W.2.property.2.1, W.2.property.2.2.1,
    availableSpecialCompactProperties_of_omegaCompatibleApartment hM B hB
      (Standard.leviTorusHom i ν J)
      (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi)
      (RenardCartan.standardLeviCentralizerDatum i C ν J) W.1 W.2.property.1
      ν hνM W.2.val W.2.property.2.1,
    W.2.property.2.2.2.2⟩

end Inheritance

include hG hB hi hD hν in
/-- Every standard Levi inherits the required geometric special vertex,
compact properties and literal preimage equality from the same point. -/
theorem availableSpecialLeviInheritance_of_omegaCompatibleApartment
    (x : D.Apartment) (hx : D.IsSpecialApartmentVertex x) :
    SpecialLeviInheritance F hi ν D x := by
  intro J hJ
  let : Mono (Standard.leviTorusHom i ν J).hom.hom.left :=
    (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi).isSplitSubtorus.mono
  let W := compatibleSpecialLeviRestriction hG B hB i hi C D hD ν hν J hJ x hx
  exact ⟨W.1, W.2.val, W.2.property⟩

end Available

end Langlands.BruhatTits.SpecialCompact
