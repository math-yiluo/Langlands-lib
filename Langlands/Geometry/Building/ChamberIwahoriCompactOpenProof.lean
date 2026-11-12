import Langlands.Geometry.Building.ChamberIwahoriCompactOpenReduction
import Langlands.Geometry.Building.ChamberIwahoriLocalReduction
import Langlands.Geometry.Building.CentralizerNormKernelConstruction
import Langlands.Geometry.Building.KPCentralizerZeroCompactOpenProof
import Langlands.GroupScheme.Rational.OpenRootGenerationReduction
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-!
# Compact openness of the actual chamber Iwahori

Openness comes from KP Corollary 8.2.6, deduced from the proved ordered
root products, together with openness of `Z(F)^0`. For compactness, the
sharp chamber decomposition writes `G(F)^♯_C` as a product of compact
root blocks and `Z^♯_x`. The group `Z^♯_x` lies in the compact image of
`Z(F)^1`. The open subgroup `P_C = Z(F)^0 · G(F)^♯_C` is closed and lies
in a compact product, so it is compact.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance chamberIwahoriProofAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance chamberIwahoriProofAmbient : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

variable (P : ParahoricBuildingData G)

local instance chamberIwahoriProofCentralizerAffine :
    IsAffine P.centralizer.Z.X.left := by
  have : IsClosedImmersion P.centralizer.j.hom.hom.left :=
    P.centralizer.isClosedSubgroup
  exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left

local instance chamberIwahoriProofCentralizer :
    TopologicalSpace (rationalPoints P.centralizer.Z) :=
  rationalPointTopology F P.centralizer.Z.X

/-- The proved rank-one factorization, for the actual torus embedding of `P`. -/
theorem hasRankOneFactorization_actual : RelativeRoot.HasRankOneFactorization P.i :=
  rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus

/-- Under the fixed-apartment axioms, the actual chamber Iwahori is open. -/
theorem isOpen_chamberIwahori_actual
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    IsOpen (P.chamberIwahori C : Set (rationalPoints G)) :=
  P.isOpen_chamberIwahori_of_openRootGeneration hP
    (RelativeRoot.openRootCentralizerGeneration_of_dynamicRootOrderedProduct
      RelativeRoot.dynamicRootOrderedProduct)
    P.centralizerZeroCompactOpen.2 hC

/-- Every point of `Z^♯_x = Z(F) ∩ G(F)^♯_x` is the image of a point of `Z(F)^1`. -/
theorem sharpCentralizer_subset_image_centralizerNormKernel
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer) (x : P.Apartment) :
    (P.apartment.sharpCentralizer {x} : Set (rationalPoints G)) ⊆
      rationalPoints.map P.centralizer.j ''
        (rationalCommonNormKernel P.centralizer.Z : Set (rationalPoints P.centralizer.Z)) := by
  rintro g ⟨hgZ, hgS⟩
  rw [← torusCentralizer_carrier_base, ← P.centralizer.isRepresentedBy.2] at hgZ
  obtain ⟨z, rfl⟩ := hgZ
  exact ⟨z, P.mem_centralizerNormKernel_of_mem_parahoric hP P.hasRankOneFactorization_actual
    (Set.singleton_nonempty x) (P.sharpFixer_le_parahoric {x} hgS), rfl⟩

/-- Under the fixed-apartment axioms, the actual chamber Iwahori is compact. -/
theorem isCompact_chamberIwahori_actual
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    IsCompact (P.chamberIwahori C : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  obtain ⟨x, hx⟩ := P.exists_mem_of_isChamber hC
  obtain ⟨ν, hν⟩ :=
    P.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter P.i
  have hsharp := (P.toValuationBuildingData.chamberSharpDecomposition_of_rankOneFactorization
    RelativeRoot.dynamicRootOrderedProduct P.hasRankOneFactorization_actual
    hP C x ν hC hx hν).1
  obtain ⟨nneg, aneg, hnegi, hnegr⟩ := P.exists_indivisiblePositiveRoots_enumeration (-ν)
  obtain ⟨npos, apos, hposi, hposr⟩ := P.exists_indivisiblePositiveRoots_enumeration ν
  have hrange := (hsharp.2.2.2.2 false nneg npos _ _ hnegi hnegr hposi hposr).2.2.2.2.2
  have hneg := P.toValuationBuildingData.isCompact_range_orderedChamberBlockProduct
    hP.topologyCompatible x false aneg
  have hpos := P.toValuationBuildingData.isCompact_range_orderedChamberBlockProduct
    hP.topologyCompatible x false apos
  have hnorm := P.toValuationBuildingData.isCompact_centralizerNormKernel_of_valuationData.image
    P.continuous_centralizerPointMap
  have hzero := P.centralizerZeroCompactOpen.1.image P.continuous_centralizerPointMap
  refine (hzero.mul ((hneg.mul hnorm).mul hpos)).of_isClosed_subset
    ((P.chamberIwahori C).isClosed_of_isOpen (P.isOpen_chamberIwahori_actual hP hC)) ?_
  change (P.parahoric C : Set (rationalPoints G)) ⊆ _
  rw [P.coe_parahoric_eq_mul C, Subgroup.coe_map]
  refine Set.mul_subset_mul_left ?_
  rw [← hrange]
  rintro _ ⟨⟨u, z, v⟩, rfl⟩
  exact ⟨_, ⟨_, ⟨u, rfl⟩, _,
    P.sharpCentralizer_subset_image_centralizerNormKernel hP x z.2, rfl⟩, _, ⟨v, rfl⟩, rfl⟩

/-- **Compact openness of the actual chamber Iwahori.** For every actual
datum `P` and every chamber `C` of its fixed apartment, `P_C` is compact and
open in the canonical topology on `G(F)`. The only premises are the
fixed-apartment axioms of the target statement. -/
theorem chamberIwahoriCompactOpen : P.ChamberIwahoriCompactOpenStatement := fun hP _ hC =>
  ⟨P.isCompact_chamberIwahori_actual hP hC, P.isOpen_chamberIwahori_actual hP hC⟩

end Langlands.Geometry.Building.ParahoricBuildingData
