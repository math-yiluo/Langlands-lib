import Langlands.BruhatTits.RationalPoints.CentralSplitQuotientCompactness
import Langlands.BruhatTits.Cartan.ActualCentralizerStructureStatement
import Langlands.GroupScheme.Reductive.CentralQuotientReductiveStatement
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.Geometry.Building.KPParahoric

/-! # Conditional compactness of the actual centralizer norm kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.BruhatTits.RationalPoints

/-- Central-quotient reductivity and anisotropic compactness give compactness
of the actual norm kernel when a maximal split torus is central. -/
theorem isCompact_rationalCommonNormKernel_of_central_maximalSplit
    (hquot : CentralQuotientReductiveStatement.{u})
    (hcompact : AnisotropicCompactnessStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {j : A.toGrp ⟶ G}
    (hj : IsMaximalSplitTorus j) (hc : IsCentral j) :
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCompact (rationalCommonNormKernel G : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨Q, q, hs, ha, _, _, hq⟩ :=
    exists_smooth_anisotropic_central_split_quotient G hj hc
  let : Smooth Q.X.hom := hs
  have hQ : IsConnectedReductive Q :=
    hquot F G Q q (SubgroupFunctor.range j) hG ha inferInstance
      ((isCentral_iff_range_le_center j).mp hc) hq
  exact centralSplitQuotientNormKernelCompactness hcompact F G hG A j hj hc Q q hQ hq

end Langlands.BruhatTits.RationalPoints

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The same factorization supplied in actual parahoric data is central and
maximal split in its represented whole-torus centralizer. -/
theorem centralizer_isCentral_maximalSplit :
    IsCentral P.centralizer.s ∧ IsMaximalSplitTorus P.centralizer.s := by
  constructor
  · apply isCentral_of_range_le_torusCentralizer P.centralizer.isRepresentedBy.1
    rw [P.centralizer.comp_eq]
    exact P.centralizer.isRepresentedBy.2.le
  · apply IsMaximalSplitTorus.of_comp P.centralizer.isClosedSubgroup
    rw [P.centralizer.comp_eq]
    exact P.isMaximalSplitTorus

/-- The whole structural targets suffice for compactness of the norm kernel
of the actual supplied centralizer, in its canonical point topology. -/
def ActualCentralizerNormKernelCompactnessReductionStatement : Prop :=
  BruhatTits.Cartan.ActualCentralizerStructureStatement.{u} →
    CentralQuotientReductiveStatement.{u} → AnisotropicCompactnessStatement.{u} →
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : IsAffine P.centralizer.Z.X.left := by
        have : IsClosedImmersion P.centralizer.j.hom.hom.left :=
          P.centralizer.isClosedSubgroup
        exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left
      letI : TopologicalSpace (rationalPoints P.centralizer.Z) :=
        rationalPointTopology F P.centralizer.Z.X
      IsCompact (rationalCommonNormKernel P.centralizer.Z :
        Set (rationalPoints P.centralizer.Z))

/-- Build the actual centralizer quotient and apply the norm-kernel adapter,
retaining all three structural proof obligations explicitly. -/
theorem actualCentralizerNormKernelCompactnessReduction :
    P.ActualCentralizerNormKernelCompactnessReductionStatement := by
  intro hstructure hquot hcompact
  have hZ := (hstructure F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus
    P.centralizer.Z P.centralizer.j P.centralizer.isClosedSubgroup
    P.centralizer.isRepresentedBy P.centralizer.s P.centralizer.comp_eq).1
  obtain ⟨hc, hm⟩ := P.centralizer_isCentral_maximalSplit
  exact BruhatTits.RationalPoints.isCompact_rationalCommonNormKernel_of_central_maximalSplit
    hquot hcompact P.centralizer.Z hZ hm hc

end Langlands.Geometry.Building.ParahoricBuildingData
