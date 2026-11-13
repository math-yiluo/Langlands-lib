import Langlands.BruhatTits.SpecialCompact.AvailableExistenceStatement
import Langlands.BruhatTits.SpecialCompact.ExistenceStatement
import Langlands.BruhatTits.SpecialCompact.CompatibleApartmentProperties
import Langlands.BruhatTits.SpecialCompact.AvailableSpecialVertexProof
import Langlands.BruhatTits.SpecialCompact.ValidTorusRebasingProof
import Langlands.BruhatTits.SpecialCompact.JointBasisReductionProof
import Langlands.Geometry.Building.BruhatTitsAvailabilityStatement

/-! # Special maximal compact subgroups from a valid corrected KP assignment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

section Transport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- Building data whose torus is the given one have, as apartment data at that torus, their
own apartment, with their apartment axioms, Axiom 4.1.2 and special vertices. -/
theorem exists_based_apartment (V : ValuationBuildingData G)
    {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
    (hS : V.S = S) (hVi : HEq V.i i) (hApt : V.SatisfiesApartmentAxioms)
    (hbdd : V.HasBoundedOpenStabilizers) :
    ∃ (C : CentralizerDatum i) (D : KPApartmentData i (localFieldOrder F)),
      HEq V.apartment D ∧ D.SatisfiesApartmentAxioms C ∧ D.HasBoundedOpenStabilizers ∧
        ((∃ x : V.Apartment, V.apartment.IsSpecialApartmentVertex x) →
          ∃ x : D.Apartment, D.IsSpecialApartmentVertex x) := by
  obtain ⟨_, SV, iV, hiV, AV, CV, hCV⟩ := V
  subst hS
  obtain rfl := eq_of_heq hVi
  exact ⟨CV, AV, HEq.rfl, hApt, hbdd, id⟩

end Transport

section Witness

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- In every prescribed omega-compatible apartment of an actual standard Levi, the special
vertex projected from an ambient special vertex is related to it by
`SpecialLeviRestriction`, when a valid corrected assignment exists. -/
theorem exists_specialLeviRestriction_of_valid (hG : IsConnectedReductive G)
    (𝔅 : KPBuildingAssignment.{u}) (h𝔅 : 𝔅.IsValid)
    {S : CommGroupScheme (Spec (CommRingCat.of F))} (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hi : IsMaximalSplitTorus i) (C : CentralizerDatum i)
    (D : KPApartmentData i (localFieldOrder F)) (hD : D.IsOmegaCompatible C)
    (hder : AffineRootSystem.derivativeRoots D.affineRoots = Set.range (rootForm i))
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ν)
    [IsAffineHom (Standard.leviScheme i ν J).X.hom]
    [Mono (Standard.leviTorusHom i ν J).hom.hom.left]
    (CM : CentralizerDatum (Standard.leviTorusHom i ν J))
    (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F))
    (hDM : DM.IsOmegaCompatible CM) (x : D.Apartment) (hx : D.IsSpecialApartmentVertex x) :
    ∃ xM : DM.Apartment, SpecialLeviRestriction F ν D x J DM xM := by
  obtain ⟨xM, hxMs, hres⟩ :=
    prescribedLeviSpecialVertex hG i hi C D hD hder ν hν J hJ CM DM hDM x hx.1
  have hM := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  have hνM : IsGenericCocharacter (Standard.leviTorusHom i ν J) ν :=
    isGenericCocharacter_leviTorusHom hν J
  have hPM := availableSpecialCompactProperties_of_omegaCompatibleApartment hM 𝔅 h𝔅
    (Standard.leviTorusHom i ν J) (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi)
    CM DM hDM ν hνM xM hxMs
  have hP := availableSpecialCompactProperties_of_omegaCompatibleApartment hG 𝔅 h𝔅
    i hi C D hD ν hν x hx
  have hle := standardLeviSpecialCompactSubgroup_le_of_compatible hG i hi C D hD
    ν hν J hJ CM DM hDM x xM hres
  have hcompact := isCompact_specialCompactLeviSubgroup_of_isCompact D ν J x hP.2.1.1
  exact ⟨xM, hxMs, hres, hPM, le_antisymm hle (hPM.2.1.2.2.2 hcompact hle)⟩

end Witness

/-- From one valid corrected KP assignment whose data for `G` are based at the given torus:
the apartment of those data, a special vertex `x` with the special compact properties of
`K_0`, and for every standard Levi a valid assignment based at the same torus in the Levi
whose apartment carries a point related to `x` by `SpecialLeviRestriction`. -/
theorem specialMaximalCompact_of_based_valid (𝔅 : KPBuildingAssignment.{u}) (h𝔅 : 𝔅.IsValid)
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S) :
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    (𝔅.datum F G hG).base.S = S → HEq (𝔅.datum F G hG).base.i i →
      IsGenericCocharacter i ν →
        ∃ (C : CentralizerDatum i) (D : KPApartmentData i (localFieldOrder F)),
          HEq (𝔅.datum F G hG).base.apartment D ∧
            D.SatisfiesApartmentAxioms C ∧ D.HasBoundedOpenStabilizers ∧
            ∃ x : D.Apartment,
              D.IsSpecialApartmentVertex x ∧
                SpecialCompactProperties F i ν (D.specialCompactSubgroup x) ∧
                ∀ J ⊆ simpleRelativeRoots i ν,
                  haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
                    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
                  haveI : Mono (Standard.leviTorusHom i ν J).hom.hom.left :=
                    (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi).isSplitSubtorus.mono
                  ∃ (hM : IsConnectedReductive (Standard.leviScheme i ν J))
                    (𝔅M : KPBuildingAssignment.{u})
                    (CM : CentralizerDatum (Standard.leviTorusHom i ν J))
                    (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F)),
                    𝔅M.IsValid ∧
                      (𝔅M.datum F (Standard.leviScheme i ν J) hM).base.S = S ∧
                      HEq (𝔅M.datum F (Standard.leviScheme i ν J) hM).base.i
                        (Standard.leviTorusHom i ν J) ∧
                      HEq (𝔅M.datum F (Standard.leviScheme i ν J) hM).base.apartment DM ∧
                      DM.SatisfiesApartmentAxioms CM ∧ DM.HasBoundedOpenStabilizers ∧
                      ∃ xM : DM.Apartment, SpecialLeviRestriction F ν D x J DM xM := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  intro hS hVi hν
  have hA : 𝔅.IsAvailableFor F G hG := h𝔅.isAvailableFor
  obtain ⟨C, D, hDe, hApt, hbdd, hx⟩ :=
    exists_based_apartment (𝔅.datum F G hG).base.toValuationBuildingData hS hVi
      hA.satisfiesPartialBuildingAxioms.apartmentAxioms hA.boundedSubgroups
  obtain ⟨x, hx⟩ := hx (availableSpecialVertexExistence F G hG 𝔅 hA)
  refine ⟨C, D, hDe, hApt, hbdd, x, hx,
    availableSpecialCompactProperties_of_omegaCompatibleApartment hG 𝔅 h𝔅 i hi C D
      hApt.omegaCompatible ν hν x hx, ?_⟩
  intro J hJ
  have : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  have : Mono (Standard.leviTorusHom i ν J).hom.hom.left :=
    (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi).isSplitSubtorus.mono
  have hM := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  obtain ⟨𝔅M, h𝔅M, hSM, hiM⟩ :=
    validAssignmentTorusRebasing 𝔅 h𝔅 F (Standard.leviScheme i ν J) hM S
      (Standard.leviTorusHom i ν J) (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi)
  have hAM := h𝔅M.isAvailableFor (F := F) (G := Standard.leviScheme i ν J) (hG := hM)
  obtain ⟨CM, DM, hDMe, hAptM, hbddM, -⟩ :=
    exists_based_apartment (𝔅M.datum F (Standard.leviScheme i ν J) hM).base.toValuationBuildingData
      hSM hiM hAM.satisfiesPartialBuildingAxioms.apartmentAxioms hAM.boundedSubgroups
  obtain ⟨xM, hxM⟩ := exists_specialLeviRestriction_of_valid hG 𝔅 h𝔅 i hi C D
    hApt.omegaCompatible hApt.derivativeRoots_affineRoots ν hν J hJ CM DM
    hAptM.omegaCompatible x hx
  exact ⟨hM, 𝔅M, CM, DM, h𝔅M, hSM, hiM, hDMe, hAptM, hbddM, xM, hxM⟩

/-- `BruhatTitsAvailabilityStatement` implies the published supplementary target
`SpecialMaximalCompactExistence`. -/
theorem specialMaximalCompactExistence_of_bruhatTitsAvailability
    (hAvail : BruhatTitsAvailabilityStatement.{u}) : SpecialMaximalCompactExistence.{u} := by
  obtain ⟨𝔅₀, h𝔅₀⟩ := hAvail
  intro F _ _ _ _ G hG S i hi ν hν
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨𝔅, h𝔅, hS, hVi⟩ := validAssignmentTorusRebasing 𝔅₀ h𝔅₀ F G hG S i hi
  obtain ⟨C, D, -, hApt, hbdd, x, hx, hP, hL⟩ :=
    specialMaximalCompact_of_based_valid 𝔅 h𝔅 F G hG S i hi ν hS hVi hν
  refine ⟨C, D, hApt, hbdd, x, hx, hP, fun J hJ => ?_⟩
  obtain ⟨-, -, CM, DM, -, -, -, -, hAptM, hbddM, xM, hxM⟩ := hL J hJ
  exact ⟨CM, DM, hAptM, hbddM, xM, hxM⟩

/-- `BruhatTitsAvailabilityStatement` gives the conclusion of
`AvailableSpecialMaximalCompactExistence` with the Levi clauses read in their own
assignments: one assignment based at `(S, i)` with apartment `D` and a special vertex `x` of
`D` with the special compact properties, and for every standard Levi an assignment available
for the Levi, based at the same torus, whose apartment has a point related to `x` by
`SpecialLeviRestriction`. -/
theorem availableSpecialMaximalCompact_perLevi_of_bruhatTitsAvailability
    (hAvail : BruhatTitsAvailabilityStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S) :
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∃ (𝔅 : KPBuildingAssignment.{u}) (D : KPApartmentData i (localFieldOrder F)),
        𝔅.IsAvailableFor F G hG ∧
          (𝔅.datum F G hG).base.S = S ∧ HEq (𝔅.datum F G hG).base.i i ∧
          HEq (𝔅.datum F G hG).base.apartment D ∧
          ∃ x : D.Apartment,
            D.IsSpecialApartmentVertex x ∧
              SpecialCompactProperties F i ν (D.specialCompactSubgroup x) ∧
              ∀ J ⊆ simpleRelativeRoots i ν,
                haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
                  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
                haveI : Mono (Standard.leviTorusHom i ν J).hom.hom.left :=
                  (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi).isSplitSubtorus.mono
                ∃ (hM : IsConnectedReductive (Standard.leviScheme i ν J))
                  (𝔅M : KPBuildingAssignment.{u})
                  (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F)),
                  𝔅M.IsAvailableFor F (Standard.leviScheme i ν J) hM ∧
                    (𝔅M.datum F (Standard.leviScheme i ν J) hM).base.S = S ∧
                    HEq (𝔅M.datum F (Standard.leviScheme i ν J) hM).base.i
                      (Standard.leviTorusHom i ν J) ∧
                    HEq (𝔅M.datum F (Standard.leviScheme i ν J) hM).base.apartment DM ∧
                    ∃ xM : DM.Apartment, SpecialLeviRestriction F ν D x J DM xM := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  intro hν
  obtain ⟨𝔅₀, h𝔅₀⟩ := hAvail
  obtain ⟨𝔅, h𝔅, hS, hVi⟩ := validAssignmentTorusRebasing 𝔅₀ h𝔅₀ F G hG S i hi
  obtain ⟨-, D, hDe, -, -, x, hx, hP, hL⟩ :=
    specialMaximalCompact_of_based_valid 𝔅 h𝔅 F G hG S i hi ν hS hVi hν
  refine ⟨𝔅, D, h𝔅.isAvailableFor, hS, hVi, hDe, x, hx, hP, fun J hJ => ?_⟩
  have : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  obtain ⟨hM, 𝔅M, -, DM, h𝔅M, hSM, hiM, hDMe, -, -, xM, hxM⟩ := hL J hJ
  exact ⟨hM, 𝔅M, DM, h𝔅M.isAvailableFor, hSM, hiM, hDMe, xM, hxM⟩

set_option linter.defProp false in
/-- Record entry: the implication `BruhatTitsAvailabilityStatement → SpecialMaximalCompactExistence`,
proved by `specialMaximalCompactExistence_of_bruhatTitsAvailability`. -/
def specialMaximalCompactExistenceOfBruhatTitsAvailability :
    BruhatTitsAvailabilityStatement.{u} → SpecialMaximalCompactExistence.{u} :=
  specialMaximalCompactExistence_of_bruhatTitsAvailability

end Langlands.BruhatTits.SpecialCompact
