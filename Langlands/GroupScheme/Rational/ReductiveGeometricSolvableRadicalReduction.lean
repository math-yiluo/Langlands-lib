import Langlands.GroupScheme.Rational.ReductiveGeometricSolvableRadicalExistsStatement
import Langlands.GroupScheme.Rational.SolvableRadicalExistenceStatement
import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusStatement
import Langlands.GroupScheme.Rational.LargestCentralSubtorusBaseChangeStatement
import Langlands.GroupScheme.Rational.SolvableSchemeComparison
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.GroupScheme.CentralIsogeny.FpqcReflectionHelpers
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Geometric solvable radicals of reductive groups from central tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace ReductiveGeometricSolvableRadical

variable {k : Type u} [Field k]

/-- A closed central torus lies in every ground-field solvable radical. -/
theorem range_le_of_isSolvableRadical {R G : GroupScheme (Spec (CommRingCat.of k))}
    {r : R ⟶ G} (hr : IsSolvableRadical r)
    (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G)
    (hA : IsTorus A.toGrp) (ha : IsClosedSubgroup a) (hca : IsCentral a) :
    SubgroupFunctor.range a ≤ SubgroupFunctor.range r :=
  hr.greatest A.toGrp a ha hA.smooth hA.connectedSpace
    (Langlands.GroupScheme.isSolvableGroupScheme_of_isCommMonObj A.toGrp)
    hca.range_isNormal

/-- The ground-field solvable radical of a connected reductive group is its
geometric solvable radical, given that normal solvable subgroups over an
algebraically closed field are central tori and that largest central subtori
are compatible with field extension. -/
theorem isGeometricSolvableRadical_of_structural
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hbase : ReductiveLargestCentralSubtorusBaseChangeStatement.{u})
    {R G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {r : R ⟶ G} (hr : IsSolvableRadical r) : IsGeometricSolvableRadical r := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  have : IsAffineHom R.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  have : Smooth R.X.hom := hr.smooth
  have : ConnectedSpace R.X.left := hr.connectedSpace
  let b := toAlgebraicClosure k
  obtain ⟨hsurj, hflat, -⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  have : Surjective b := hsurj
  have : Flat b := hflat
  -- The base change of `G` is reductive over the algebraically closed field.
  have hGK : IsPseudoReductive ((GroupScheme.baseChange b).obj G) :=
    { smooth := by
        change Smooth (pullback.snd G.X.hom b)
        infer_instance
      isAffineHom := by
        change IsAffineHom (pullback.snd G.X.hom b)
        infer_instance
      connectedSpace := G.connectedSpace_baseChange_of_smooth_affine b
      hasTrivialUnipotentRadical := hG.hasTrivialGeometricUnipotentRadical }
  -- The base change of the radical keeps every property except greatestness.
  have hcl : IsClosedSubgroup ((GroupScheme.baseChange b).map r) :=
    hr.isClosedSubgroup.baseChange b
  have hsm : Smooth ((GroupScheme.baseChange b).obj R).X.hom := by
    change Smooth (pullback.snd R.X.hom b)
    infer_instance
  have hco : ConnectedSpace ((GroupScheme.baseChange b).obj R).X.left :=
    R.connectedSpace_baseChange_of_smooth_affine b
  have hsol : IsSolvableGroupScheme ((GroupScheme.baseChange b).obj R) :=
    ((((RelativeRoot.isSolvableScheme_iff_isSolvableGroupScheme hr.smooth).mpr
      hr.isSolvableGroupScheme).baseChange b)).isSolvableGroupScheme
  have hnor : (SubgroupFunctor.range ((GroupScheme.baseChange b).map r)).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hr.isNormal.baseChange b
  -- The radical is a central torus, checked after base change.
  obtain ⟨hRKt, hRKc⟩ := htorus (AlgebraicClosure k) _ hGK _ _ hcl hsm hco hsol hnor
  have hRt : IsTorus R := IsTorus.of_baseChange (K := AlgebraicClosure k) hRKt
  have hRc : IsCentral r := IsCentral.of_baseChange b hRKc
  let Rc : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { toGrp := R, comm := hRt.isCommMonObj }
  have hz : IsLargestCentralSubtorus (Z := Rc) r :=
    { isTorus := hRt
      isClosedSubgroup := hr.isClosedSubgroup
      isCentral := hRc
      greatest := fun A a hA ha hca => range_le_of_isSolvableRadical hr A a hA ha hca }
  have hzK := hbase k (AlgebraicClosure k) G Rc r hG hz
  refine ⟨hr, hcl, hsm, hco, hsol, hnor, ?_⟩
  intro N n hn hNs hNc hNsol hNn
  obtain ⟨hNt, hNcen⟩ := htorus (AlgebraicClosure k) _ hGK N n hn hNs hNc hNsol hNn
  let Nc : CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))) :=
    { toGrp := N, comm := hNt.isCommMonObj }
  exact hzK.greatest Nc n hNt hn hNcen

end ReductiveGeometricSolvableRadical

/-- The geometric solvable radical existence target for connected reductive groups
follows from ground-field radical existence, central tori of normal solvable
subgroups over algebraically closed fields, and field-extension compatibility of
largest central subtori. -/
def ReductiveGeometricSolvableRadicalFromStructureStatement : Prop :=
  SolvableRadicalExistenceStatement.{u} → AlgClosedReductiveNormalSolvableTorusStatement.{u} →
    ReductiveLargestCentralSubtorusBaseChangeStatement.{u} →
      ReductiveGeometricSolvableRadicalExistsStatement.{u}

/-- The ground-field solvable radical of a connected reductive group is a geometric
solvable radical. -/
theorem reductiveGeometricSolvableRadicalExists_of_structure :
    ReductiveGeometricSolvableRadicalFromStructureStatement.{u} := by
  intro hexists htorus hbase k _ G hG
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨R, r, hr⟩ := hexists k G
  exact ⟨R, r, ReductiveGeometricSolvableRadical.isGeometricSolvableRadical_of_structural
    htorus hbase hG hr⟩

end Langlands.GroupScheme
