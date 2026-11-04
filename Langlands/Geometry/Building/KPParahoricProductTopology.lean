import Langlands.Geometry.Building.KPParahoricProduct
import Langlands.Geometry.Building.KPRootFixerTopology
import Langlands.Geometry.Building.ChamberIwahori

/-! # Canonical topology on actual full-parahoric multiplication maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance kpParahoricProductTopologyAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance kpParahoricProductTopologyAmbient : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

variable (P : ParahoricBuildingData G)

local instance kpParahoricProductTopologyCentralizerAffine :
    IsAffine P.centralizer.Z.X.left := by
  have : IsClosedImmersion P.centralizer.j.hom.hom.left :=
    P.centralizer.isClosedSubgroup
  exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left

local instance kpParahoricProductTopologyCentralizer :
    TopologicalSpace (rationalPoints P.centralizer.Z) :=
  rationalPointTopology F P.centralizer.Z.X

/-- Actual centralizer inclusion is continuous for both canonical point topologies. -/
theorem continuous_centralizerPointMap :
    Continuous (rationalPoints.map P.centralizer.j) :=
  continuous_rationalPointMap F P.centralizer.j.hom.hom

/-- Multiplication of the supplied centralizer-zero and sharp factors is continuous. -/
theorem continuous_parahoricProductMap (Ω : Set P.Apartment) :
    Continuous (P.parahoricProductMap Ω) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  apply continuous_induced_rng.mpr
  exact ((P.continuous_centralizerPointMap.comp
    (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd))

/-- The original surjective product map, bundled with its canonical continuity. -/
def parahoricProductContinuousMap (Ω : Set P.Apartment) :
    C(P.centralizerZero × P.sharpFixer Ω, P.parahoric Ω) :=
  ⟨P.parahoricProductMap Ω, P.continuous_parahoricProductMap Ω⟩

@[simp] theorem parahoricProductContinuousMap_apply (Ω : Set P.Apartment)
    (zh : P.centralizerZero × P.sharpFixer Ω) :
    P.parahoricProductContinuousMap Ω zh = P.parahoricProductMap Ω zh := rfl

/-- Compactness transfers from both actual factors to their full parahoric.
This lemma retains both compactness premises as separate obligations. -/
theorem isCompact_parahoric_of_factors (Ω : Set P.Apartment)
    (hZ : IsCompact (P.centralizerZero : Set (rationalPoints P.centralizer.Z)))
    (hsharp : IsCompact (P.sharpFixer Ω : Set (rationalPoints G))) :
    IsCompact (P.parahoric Ω : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  rw [P.coe_parahoric_eq_mul Ω]
  exact (hZ.image P.continuous_centralizerPointMap).mul hsharp

/-- The three actual unipotent/central factors multiply continuously. -/
theorem continuous_iwahoriUnipotentProduct (C : Set P.Apartment)
    (ν : cocharacterLattice P.S) :
    Continuous (P.iwahoriUnipotentProduct C ν) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  exact ((continuous_subtype_val.comp continuous_fst).mul
    (P.continuous_centralizerPointMap.comp
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))).mul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))

/-- Full-central-factor ordered chamber multiplication is continuous at either depth. -/
theorem continuous_orderedIwahoriChamberProduct (x : P.Apartment) (strict : Bool)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice P.S)
    (apos : Fin npos → characterLattice P.S) :
    Continuous (P.orderedIwahoriChamberProduct x strict aneg apos) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  exact (((P.toValuationBuildingData.continuous_orderedChamberBlockProduct x strict aneg).comp
    continuous_fst).mul
      (P.continuous_centralizerPointMap.comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))).mul
    ((P.toValuationBuildingData.continuous_orderedChamberBlockProduct x strict apos).comp
      (continuous_snd.comp continuous_snd))

/-- Full-central-factor ordered facet multiplication is continuous on every subset. -/
theorem continuous_orderedIwahoriFacetProduct (Ω : Set P.Apartment)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice P.S)
    (apos : Fin npos → characterLattice P.S) :
    Continuous (P.orderedIwahoriFacetProduct Ω aneg apos) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  exact (((P.toValuationBuildingData.continuous_orderedFacetBlockProduct Ω true aneg).comp
    continuous_fst).mul
      (P.continuous_centralizerPointMap.comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))).mul
    ((P.toValuationBuildingData.continuous_orderedFacetBlockProduct Ω false apos).comp
      (continuous_snd.comp continuous_snd))

/-- V 7 and compactness of the actual centralizer-zero factor give compact ranges
for finite full Iwahori chamber products. No equality with the Iwahori is asserted. -/
theorem isCompact_range_orderedIwahoriChamberProduct
    (hP : P.apartment.IsTopologyCompatible)
    (hZ : IsCompact (P.centralizerZero : Set (rationalPoints P.centralizer.Z)))
    (x : P.Apartment) (strict : Bool)
    {nneg npos : ℕ} (aneg : Fin nneg → relativeRoots P.i)
    (apos : Fin npos → relativeRoots P.i) :
    IsCompact (Set.range (P.orderedIwahoriChamberProduct x strict
      (fun j => (aneg j : characterLattice P.S))
      (fun j => (apos j : characterLattice P.S)))) := by
  let : CompactSpace P.centralizerZero := isCompact_iff_compactSpace.mp hZ
  let (j : Fin nneg) : CompactSpace (P.apartment.chamberRootBlock x strict (aneg j)) :=
    isCompact_iff_compactSpace.mp
      (P.toValuationBuildingData.isCompact_chamberRootBlock hP x strict (aneg j))
  let (j : Fin npos) : CompactSpace (P.apartment.chamberRootBlock x strict (apos j)) :=
    isCompact_iff_compactSpace.mp
      (P.toValuationBuildingData.isCompact_chamberRootBlock hP x strict (apos j))
  exact isCompact_range (P.continuous_orderedIwahoriChamberProduct x strict _ _)

/-- The facet analogue requires explicit nonemptiness, V 7 and compactness of the
actual centralizer-zero factor; it retains negative strict and positive weak depth. -/
theorem isCompact_range_orderedIwahoriFacetProduct
    (hP : P.apartment.IsTopologyCompatible)
    (hZ : IsCompact (P.centralizerZero : Set (rationalPoints P.centralizer.Z)))
    {Ω : Set P.Apartment} {x : P.Apartment} (hx : x ∈ Ω)
    {nneg npos : ℕ} (aneg : Fin nneg → relativeRoots P.i)
    (apos : Fin npos → relativeRoots P.i) :
    IsCompact (Set.range (P.orderedIwahoriFacetProduct Ω
      (fun j => (aneg j : characterLattice P.S))
      (fun j => (apos j : characterLattice P.S)))) := by
  let : CompactSpace P.centralizerZero := isCompact_iff_compactSpace.mp hZ
  let (j : Fin nneg) : CompactSpace (P.apartment.facetRootBlock Ω true (aneg j)) :=
    isCompact_iff_compactSpace.mp
      (P.toValuationBuildingData.isCompact_facetRootBlock hP hx true (aneg j))
  let (j : Fin npos) : CompactSpace (P.apartment.facetRootBlock Ω false (apos j)) :=
    isCompact_iff_compactSpace.mp
      (P.toValuationBuildingData.isCompact_facetRootBlock hP hx false (apos j))
  exact isCompact_range (P.continuous_orderedIwahoriFacetProduct Ω _ _)

end Langlands.Geometry.Building.ParahoricBuildingData
