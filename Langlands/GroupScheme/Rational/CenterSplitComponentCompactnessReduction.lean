import Langlands.GroupScheme.Rational.CenterSplitComponentCompactnessStatement
import Langlands.GroupScheme.Rational.CenterQuotientModel
import Langlands.GroupScheme.Rational.MultiplicativeTypeSplitQuotientAnisotropyStatement
import Langlands.GroupScheme.Reductive.CenterExistenceProof
import Langlands.GroupScheme.Reductive.CenterMultiplicativeTypeStatement
import Langlands.GroupScheme.AffineNormalSubgroupQuotientStatement
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.Torus.OpenSections

/-! # Reduction of full-center quotient compactness to structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Full-center multiplicative type, actual affine quotient existence,
split-quotient anisotropy, and anisotropic compactness imply the unchanged
full-center point quotient compactness statement. -/
def CenterSplitComponentCompactnessReductionStatement : Prop :=
  CenterMultiplicativeTypeStatement.{u} →
    AffineNormalSubgroupQuotientStatement.{u} →
    MultiplicativeTypeSplitQuotientAnisotropyStatement.{u} →
    AnisotropicCompactnessStatement.{u} →
    CenterSplitComponentCompactnessStatement.{u}

/-- Construct the actual full-center quotient, its open sections, and its
canonical point homeomorphism, retaining each structural input explicitly. -/
theorem centerSplitComponentCompactnessReduction :
    CenterSplitComponentCompactnessReductionStatement.{u} := by
  intro hcenter hquot hstruct hcompact F _ _ _ _ M hM A i hi
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : Smooth M.X.hom := hM.smooth
  obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence F M hM
  let : IsClosedImmersion z.hom.hom.left := hz.1
  let : Mono z.hom.hom := hz.isRepresentedBy.1
  let : IsAffine Z.X.left := isAffine_of_isAffineHom z.hom.hom.left
  let : IsAffineHom Z.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  let : LocallyOfFiniteType Z.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  have hile : SubgroupFunctor.range i ≤ center M := by
    rintro U _ ⟨a, rfl⟩
    exact hi.isCentralSplitTorus.isCentral U a
  let j : A.toGrp ⟶ Z := hz.isRepresentedBy.factorHom i hile
  have hjz : j ≫ z = i := hz.isRepresentedBy.factorHom_comp i hile
  have hjclosed : IsClosedSubgroup j := IsClosedSubgroup.of_comp hz.1 (by
    rw [hjz]
    exact hi.1.1.2)
  have hjcentral : IsCentral j := IsCentral.of_comp hz.isRepresentedBy.1 (by
    rw [hjz]
    exact hi.isCentralSplitTorus.isCentral)
  obtain ⟨C, q, hClft, hCaff, hq⟩ :=
    hquot F Z A.toGrp j hjclosed hjcentral.range_isNormal
  let : IsAffineHom C.X.hom := hCaff
  let : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let : LocallyOfFiniteType C.X.hom := hClft
  let : IsClosedImmersion j.hom.hom.left := hjclosed
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have hs : HasOpenSectionsAtPoints F F q.hom.hom :=
    SplitTorusQuotient.hasOpenSectionsAtPoints j q hq.2.2.2 hi.1.1.1
  have hC := hstruct.centerQuotient hz (hcenter F M Z z hM hz) hi hjz q hq
  let : TopologicalSpace (rationalPoints C) := rationalPointTopology F C.X
  let : CompactSpace (rationalPoints C) := hC.compactSpace hcompact
  let : TopologicalSpace
      (CentralPointQuotient i hi.isCentralSplitTorus.isCentral) :=
    centralPointQuotientTopology i hi.isCentralSplitTorus.isCentral
  exact (centralPointQuotientModelHomeomorph z hz i
    hi.isCentralSplitTorus.isCentral j hjz q hq hs).symm.toHomeomorph.compactSpace

end Langlands.GroupScheme
