import Langlands.Representation.Plancherel.RenardLeviCentralizerCompatibility
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof
import Langlands.GroupScheme.SimplyConnected.DerivedCoverProof

/-! # Parahoric data on the same restricted standard-Levi apartment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ParahoricBuildingData G) (ν : cocharacterLattice B.S)
  (hν : IsGenericCocharacter B.i ν) (J : Set (characterLattice B.S))
  (hJ : J ⊆ simpleRelativeRoots B.i ν)

local instance : IsAffineHom (Standard.leviScheme B.i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom B.i ν J).isAffineHom

local instance : Mono (Standard.leviTorusHom B.i ν J).hom.hom.left :=
  mono_of_isMaximalSplitTorus
    (Standard.isMaximalSplitTorus_leviTorusHom B.i ν J B.isMaximalSplitTorus)

variable (DM : KPApartmentData (Standard.leviTorusHom B.i ν J) (localFieldOrder F))
  (hres : ∀ yM : DM.Apartment, ∃ y : B.Apartment,
    IsLeviRestriction (Standard.leviHom B.i ν J) y yM)

/-- The actual standard Levi receives parahoric data on the prescribed restricted
apartment. Its centralizer, torus map, valuation and unramified centralizer zero
data remain the ambient ones; only a Levi derived cover is newly chosen. -/
def standardLeviParahoricData : ParahoricBuildingData (Standard.leviScheme B.i ν J) := by
  let hM := (standardLeviSplitComponentStatement F G B.isConnectedReductive B.S B.i
    B.isMaximalSplitTorus ν hν J hJ).1
  let hc := simplyConnectedDerivedCoverExistence F (Standard.leviScheme B.i ν J) hM
  let D := hc.choose
  let C := hc.choose_spec.choose
  let d := hc.choose_spec.choose_spec.choose
  let π := hc.choose_spec.choose_spec.choose_spec.choose
  have hcover : IsSimplyConnectedDerivedCover d π :=
    hc.choose_spec.choose_spec.choose_spec.choose_spec
  exact {
    isConnectedReductive := hM
    S := B.S
    i := Standard.leviTorusHom B.i ν J
    isMaximalSplitTorus :=
      Standard.isMaximalSplitTorus_leviTorusHom B.i ν J B.isMaximalSplitTorus
    apartment := DM
    centralizer := standardLeviCentralizerDatum B.i B.centralizer ν J
    isOmegaCompatible := isOmegaCompatible_standardLevi_of_restriction B.i B.centralizer ν J
      B.apartment DM B.isOmegaCompatible hres
    zeroDatum := {
      isMaximalSplitTorus :=
        Standard.isMaximalSplitTorus_leviTorusHom B.i ν J B.isMaximalSplitTorus
      isRepresentedBy :=
        isRepresentedBy_standardLeviCentralizerFactor B.i ν J B.centralizer.j
          B.centralizer.isRepresentedBy
      centralizerDatum := B.zeroDatum.centralizerDatum
      D := D
      C := C
      d := d
      π := π
      isSimplyConnectedDerivedCover := hcover } }

@[simp]
theorem standardLeviParahoricData_torus :
    (standardLeviParahoricData B ν hν J hJ DM hres).S = B.S := rfl

@[simp]
theorem standardLeviParahoricData_torusHom :
    (standardLeviParahoricData B ν hν J hJ DM hres).i =
      Standard.leviTorusHom B.i ν J := rfl

@[simp]
theorem standardLeviParahoricData_apartment :
    (standardLeviParahoricData B ν hν J hJ DM hres).apartment = DM := rfl

@[simp]
theorem standardLeviParahoricData_centralizer :
    (standardLeviParahoricData B ν hν J hJ DM hres).centralizer =
      standardLeviCentralizerDatum B.i B.centralizer ν J := rfl

@[simp]
theorem standardLeviParahoricData_centralizerZero :
    (standardLeviParahoricData B ν hν J hJ DM hres).centralizerZero =
      B.centralizerZero := rfl

end Langlands.Plancherel.RenardCartan
