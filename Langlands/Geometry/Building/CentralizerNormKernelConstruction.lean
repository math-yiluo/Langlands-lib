import Langlands.Geometry.Building.KPCentralizerNormKernelCompactness
import Langlands.Geometry.Building.SharpFixerBoundednessAssembly
import Langlands.Geometry.Building.SharpFixerBoundednessStructuralReduction
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.QuasiSplitCentralizerTorus
import Langlands.GroupScheme.Reductive.CentralQuotientReductiveProof
import Langlands.GroupScheme.Rational.AnisotropicCompactnessProof
import Langlands.Representation.Plancherel.RationalNormKernelTopology

/-! # The compact open norm kernel of the actual split-torus centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

private instance normKernelAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

private instance normKernelCentralizerAffine : IsAffine B.centralizer.Z.X.left := by
  have : IsClosedImmersion B.centralizer.j.hom.hom.left := B.centralizer.isClosedSubgroup
  exact isAffine_of_isAffineHom B.centralizer.j.hom.hom.left

private instance normKernelCentralizerTopology :
    TopologicalSpace (rationalPoints B.centralizer.Z) :=
  rationalPointTopology F B.centralizer.Z.X

/-- The supplied closed representative of the whole actual centralizer is
connected reductive, by dynamic centralizer reductivity. -/
theorem isConnectedReductive_centralizer : IsConnectedReductive B.centralizer.Z :=
  B.isMaximalSplitTorus.1.1.isConnectedReductive_centralizer_of_dynamic
    dynamicCentralizerReductive B.isConnectedReductive B.i B.centralizer.j
    B.centralizer.isRepresentedBy B.centralizer.isClosedSubgroup

/-- The actual norm kernel of the whole centralizer is compact in its canonical
rational-point topology. No structural or apartment premise remains. -/
theorem isCompact_centralizerNormKernel_of_valuationData :
    IsCompact (rationalCommonNormKernel B.centralizer.Z :
      Set (rationalPoints B.centralizer.Z)) := by
  obtain ⟨hc, hm⟩ := B.centralizer_isCentral_maximalSplit
  exact BruhatTits.RationalPoints.isCompact_rationalCommonNormKernel_of_central_maximalSplit
    centralQuotientReductive anisotropicCompactness_proof B.centralizer.Z
    B.isConnectedReductive_centralizer hm hc

/-- The actual centralizer norm kernel has algebraically bounded image in the
original ambient group. -/
theorem isAlgebraicallyBounded_image_centralizerNormKernel :
    IsAlgebraicallyBounded F G.X (rationalPoints.map B.centralizer.j ''
      (rationalCommonNormKernel B.centralizer.Z : Set (rationalPoints B.centralizer.Z))) :=
  B.isAlgebraicallyBounded_image_centralizerNormKernel_of_isCompact
    B.isCompact_centralizerNormKernel_of_valuationData

/-- The actual centralizer norm kernel is also open in the same topology. -/
theorem isOpen_centralizerNormKernel :
    IsOpen (rationalCommonNormKernel B.centralizer.Z :
      Set (rationalPoints B.centralizer.Z)) := by
  have : Smooth B.centralizer.Z.X.hom := B.isConnectedReductive_centralizer.smooth
  exact isOpen_rationalCommonNormKernel B.centralizer.Z

/-- Bundle the unchanged actual norm kernel as a compact open subgroup, together
with algebraic boundedness of its image under the original inclusion. -/
def centralizerNormKernelData :
    {K : OpenSubgroup (rationalPoints B.centralizer.Z) //
      K.toSubgroup = rationalCommonNormKernel B.centralizer.Z ∧
      IsCompact (K : Set (rationalPoints B.centralizer.Z)) ∧
      IsAlgebraicallyBounded F G.X
        (rationalPoints.map B.centralizer.j '' (K : Set (rationalPoints B.centralizer.Z)))} :=
  ⟨⟨rationalCommonNormKernel B.centralizer.Z, B.isOpen_centralizerNormKernel⟩,
    rfl, B.isCompact_centralizerNormKernel_of_valuationData, B.isAlgebraicallyBounded_image_centralizerNormKernel⟩

end Langlands.Geometry.Building.ValuationBuildingData
