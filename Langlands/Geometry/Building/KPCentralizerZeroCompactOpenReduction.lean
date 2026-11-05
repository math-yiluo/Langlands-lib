import Langlands.Geometry.Building.KPCentralizerNormKernelCompactness
import Langlands.Geometry.Building.KPCentralizerZeroCompactOpenStatement
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups

/-! # Compact openness of the actual centralizer-zero subgroup from openness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The whole structural targets and openness of the actual centralizer-zero
subgroup suffice for the exact compact-openness target. -/
def CentralizerZeroCompactOpenReductionStatement : Prop :=
  BruhatTits.Cartan.ActualCentralizerStructureStatement.{u} →
    CentralQuotientReductiveStatement.{u} → AnisotropicCompactnessStatement.{u} →
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : IsAffine P.centralizer.Z.X.left := by
        have : IsClosedImmersion P.centralizer.j.hom.hom.left :=
          P.centralizer.isClosedSubgroup
        exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left
      letI : TopologicalSpace (rationalPoints P.centralizer.Z) :=
        rationalPointTopology F P.centralizer.Z.X
      IsOpen (P.centralizerZero : Set (rationalPoints P.centralizer.Z)) →
        P.CentralizerZeroCompactOpenStatement

/-- An open subgroup is closed, and the actual centralizer-zero subgroup lies in
the compact actual norm kernel. -/
theorem centralizerZeroCompactOpenReduction :
    P.CentralizerZeroCompactOpenReductionStatement := by
  intro hstructure hquot hcompact hopen
  have hK := P.actualCentralizerNormKernelCompactnessReduction hstructure hquot hcompact
  have hZ := (hstructure F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus
    P.centralizer.Z P.centralizer.j P.centralizer.isClosedSubgroup
    P.centralizer.isRepresentedBy P.centralizer.s P.centralizer.comp_eq).1
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine P.centralizer.Z.X.left := by
    have : IsClosedImmersion P.centralizer.j.hom.hom.left :=
      P.centralizer.isClosedSubgroup
    exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left
  let : TopologicalSpace (rationalPoints P.centralizer.Z) :=
    rationalPointTopology F P.centralizer.Z.X
  let : Smooth P.centralizer.Z.X.hom := hZ.smooth
  let : IsTopologicalGroup (rationalPoints P.centralizer.Z) :=
    rationalPoint_isTopologicalGroup F P.centralizer.Z
  refine ⟨?_, hopen⟩
  exact hK.of_isClosed_subset (P.centralizerZero.isClosed_of_isOpen hopen)
    P.zeroDatum.centralizerZero_le_rationalCommonNormKernel

end Langlands.Geometry.Building.ParahoricBuildingData
