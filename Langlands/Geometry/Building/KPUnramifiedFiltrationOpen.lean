import Langlands.Geometry.Building.KPIntegerRootFiltrationOpen
import Langlands.Geometry.Building.KPCharacterKernelTopology
import Langlands.Geometry.Building.KPLocalMoyPrasadGroups
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.OpenRootGenerationTopologicalField
import Langlands.GroupScheme.Rational.QuasiSplitCentralizerTorus

/-! # Openness for supplied building filtrations over the maximal unramified field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

local instance unramifiedFiltrationValued : Valued (UnramifiedClosure F) ℝ≥0 :=
  fixedFieldValued F

private instance ambientAffine : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
private instance centralizerAffine : IsAffine B.centralizer.Z.X.left := by
  have : IsClosedImmersion B.centralizer.j.hom.hom.left := B.centralizer.isClosedSubgroup
  exact isAffine_of_isAffineHom B.centralizer.j.hom.hom.left

local instance ambientTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology (UnramifiedClosure F) H.X
local instance centralizerTopology : TopologicalSpace (rationalPoints B.centralizer.Z) :=
  rationalPointTopology (UnramifiedClosure F) B.centralizer.Z.X

/-- Integer normalization preserves the open character kernel in the actual topology. -/
theorem isOpen_integerCharacterValuationKernel :
    IsOpen (characterValuationKernel (valuation F) B.centralizer.Z :
      Set (rationalPoints B.centralizer.Z)) := by
  have he : characterValuationKernel (valuation F) B.centralizer.Z =
      characterValuationKernel (fixedFieldValuation F) B.centralizer.Z := by
    ext z
    simp only [mem_characterValuationKernel]
    exact forall_congr' fun χ => (valuation_isEquiv F).eq_one_iff_eq_one
  rw [he]
  apply isOpen_characterValuationKernel_of_isConnectedReductive
  exact B.isMaximalSplitTorus.1.1.isConnectedReductive_centralizer_of_dynamic
    dynamicCentralizerReductive B.isConnectedReductive B.i B.centralizer.j
    B.centralizer.isRepresentedBy B.centralizer.isClosedSubgroup

/-- Every actual root filtration is relatively open for the fixed-field topology. -/
theorem isOpen_rootFiltration (x : B.Apartment) (α : relativeRoots B.i) (r : ℝ) :
    IsOpen (((↑) : B.rootGroup α → rationalPoints H) ⁻¹'
      (B.filtration x α r : Set (rationalPoints H))) :=
  B.isOpen_filtration B.isOpen_integerCharacterValuationKernel
    (exists_order_ne_zero F) x α r

/-- The actual root filtration as an open subgroup in the fixed-field topology. -/
def rootFiltrationOpenSubgroup (x : B.Apartment) (α : relativeRoots B.i) (r : ℝ) :
    OpenSubgroup (B.rootGroup α) where
  toSubgroup := (B.filtration x α r).subgroupOf (B.rootGroup α)
  isOpen' := B.isOpen_rootFiltration x α r

/-- Topological root-centralizer generation reduces openness to the torus term. -/
theorem isOpen_moyPrasad_of_isOpen_torus (x : B.Apartment) (r : ℝ≥0)
    (hT : IsOpen (B.centralizerTorusFiltration hZ r :
      Set (rationalPoints B.centralizer.Z))) :
    IsOpen (B.moyPrasad hZ x r : Set (rationalPoints H)) := by
  rw [B.moyPrasad_eq_sup_iSup hZ x r]
  exact RelativeRoot.topologicalRootCentralizerGeneration (UnramifiedClosure F) H
    B.isConnectedReductive B.S B.i B.isMaximalSplitTorus B.centralizer.Z B.centralizer.j
    B.centralizer.isRepresentedBy B.centralizer.isClosedSubgroup
    (fun α => B.filtration x α r) (B.centralizerTorusFiltration hZ r)
    (fun α => B.filtration_le_rootGroup x α r)
    (fun α => B.isOpen_rootFiltration x α r) hT

end Langlands.Geometry.Building.MaximalUnramified.BuildingData
