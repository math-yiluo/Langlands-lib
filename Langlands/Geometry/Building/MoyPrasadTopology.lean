import Langlands.Geometry.Building.KPMoyPrasadFiltration
import Langlands.Geometry.Building.KPFiltrationTopology
import Langlands.Geometry.Building.KPParahoricFixerComparison
import Langlands.Geometry.Building.BoundedOpenStabilizerAssembly
import Langlands.Geometry.Building.CentralizerNormKernelConstruction
import Langlands.Geometry.Building.SharpFixerBoundednessProof
import Langlands.GroupScheme.Rational.OpenRootGenerationProof

/-! # Compact open original Moy–Prasad subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Set
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} (Zf : P.CentralizerFiltration)

local instance moyPrasadTopologyAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance moyPrasadTopologyAmbient : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

local instance moyPrasadTopologyCentralizerAffine : IsAffine P.centralizer.Z.X.left := by
  have : IsClosedImmersion P.centralizer.j.hom.hom.left := P.centralizer.isClosedSubgroup
  exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left
local instance moyPrasadTopologyCentralizer :
    TopologicalSpace (rationalPoints P.centralizer.Z) :=
  rationalPointTopology F P.centralizer.Z.X

/-- V7 and openness of the supplied centralizer-depth groups make each
literal original Moy–Prasad group open by actual root-centralizer generation.
No commutator, covariance or product-covering hypothesis is needed. -/
theorem isOpen_moyPrasad
    (hP : P.apartment.IsTopologyCompatible) (hZo : Zf.IsOpenFiltration)
    (x : P.Apartment) (r : NNReal) :
    IsOpen (Zf.moyPrasad x r : Set (rationalPoints G)) := by
  rw [moyPrasad, P.apartment.sharpFiltration_eq_iSup]
  exact RelativeRoot.openRootCentralizerGeneration F G P.isConnectedReductive
    P.S P.i P.isMaximalSplitTorus P.centralizer.Z P.centralizer.j
    P.centralizer.isRepresentedBy P.centralizer.isClosedSubgroup
    (fun a => P.filtration x a.1 r) (Zf.filtration r)
    (fun a => P.filtration_le_rootGroup x a r)
    (fun a => (P.toValuationBuildingData.filtrationOpenSubgroup hP x a r).isOpen')
    (hZo r)

/-- Each original depth subgroup lies in the bounded original point fixer.
The apartment axioms suffice; no filtration algebra or openness is used. -/
theorem isAlgebraicallyBounded_moyPrasad
    (hP : P.SatisfiesApartmentAxioms) (x : P.Apartment) (r : NNReal) :
    IsAlgebraicallyBounded F G.X (Zf.moyPrasad x r : Set (rationalPoints G)) := by
  have hb := P.toValuationBuildingData.isAlgebraicallyBounded_compactStabilizer_apartmentMap
    hP.topologyCompatible (P.toValuationBuildingData.sharpFixerBoundedness hP)
    P.toValuationBuildingData.isAlgebraicallyBounded_image_centralizerNormKernel x
  exact hb.mono ((Zf.moyPrasad_le_parahoricAt x r).trans
    (P.parahoricAt_le_compactStabilizer hP.topologyCompatible x))

/-- The open subgroup is exactly the original generated depth subgroup,
with the canonical ambient rational-point topology. -/
def moyPrasadOpenSubgroup
    (hP : P.apartment.IsTopologyCompatible) (hZo : Zf.IsOpenFiltration)
    (x : P.Apartment) (r : NNReal) : OpenSubgroup (rationalPoints G) where
  toSubgroup := Zf.moyPrasad x r
  isOpen' := Zf.isOpen_moyPrasad hP hZo x r

@[simp]
theorem moyPrasadOpenSubgroup_toSubgroup
    (hP : P.apartment.IsTopologyCompatible) (hZo : Zf.IsOpenFiltration)
    (x : P.Apartment) (r : NNReal) :
    (Zf.moyPrasadOpenSubgroup hP hZo x r).toSubgroup = Zf.moyPrasad x r := rfl

/-- Boundedness and subgroup openness make the same original depth group
compact at every apartment point and finite nonnegative depth. -/
theorem isCompact_moyPrasad
    (hP : P.SatisfiesApartmentAxioms) (hZo : Zf.IsOpenFiltration)
    (x : P.Apartment) (r : NNReal) :
    IsCompact (Zf.moyPrasad x r : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have hc := (Zf.isAlgebraicallyBounded_moyPrasad hP x r).isCompact_closure G.X
  exact hc.of_isClosed_subset
    ((Zf.moyPrasad x r).isClosed_of_isOpen (Zf.isOpen_moyPrasad hP.topologyCompatible hZo x r))
    subset_closure

end Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration
