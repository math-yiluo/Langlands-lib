import Langlands.GroupScheme.Reductive.CentralTorusSemisimpleQuotientStatement
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Reductive.FiniteCenterOfNoCentralSubgroups
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Rational.SolvableRadicalQuotient
import Langlands.GroupScheme.Rational.ReductiveGeometricSolvableRadicalReduction

/-! # Central torus semisimple quotients from geometric solvable radicals -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section FiniteCenter

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Absence of smooth connected solvable normal subgroups forces finiteness
of the full scheme-theoretic centre. -/
theorem HasTrivialSolvableRadical.hasFiniteCenter
    (hG : HasTrivialSolvableRadical G) : HasFiniteCenter G := by
  obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence_of_isAffineHom
    (inferInstance : IsAffineHom G.X.hom)
  refine ⟨Z, z, hz, hz.isFinite_of_no_smooth_connected_central_subgroups ?_⟩
  intro H h hh hs hc hcentral
  have : IsClosedImmersion h.hom.hom.left := hh
  have : Mono h.hom.hom := Over.mono_of_mono_left _
  have : IsCommMonObj H.X := hcentral.isCommMonObj
  exact hG H h hh hs hc (isSolvableGroupScheme_of_isCommMonObj H)
    hcentral.range_isNormal

end FiniteCenter

section Quotient

variable {k : Type u} [Field k]
    {R G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {r : R ⟶ G}

/-- A quotient by an actual geometric solvable radical is semisimple,
including finiteness of its full centre. -/
theorem IsGeometricSolvableRadical.isSemisimple_quotient
    (hr : IsGeometricSolvableRadical r) (q : G ⟶ Q) [IsAffineHom Q.X.hom]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q) :
    IsSemisimple Q := by
  have hQ : IsConnectedReductive Q := hr.isConnectedReductive_quotient q hq
  have hQbar := hQ.baseChange_toAlgebraicClosure
  have : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj Q).X.hom :=
    hQbar.isAffineHom
  have : Smooth ((GroupScheme.baseChange (toAlgebraicClosure k)).obj Q).X.hom :=
    hQbar.smooth
  exact IsSemisimple.of_fieldExtension (K := AlgebraicClosure k)
    ⟨hQbar, (hr.hasTrivialGeometricSolvableRadical_quotient q hq).hasFiniteCenter⟩

end Quotient

section Structure

variable {k : Type u} [Field k]
    {R G : GroupScheme (Spec (CommRingCat.of k))} {r : R ⟶ G}

/-- The algebraically closed normal-solvable-torus theorem makes a supplied
geometric solvable radical of a reductive group a central torus over its field. -/
theorem IsGeometricSolvableRadical.isTorus_and_isCentral_of_structural
    (hr : IsGeometricSolvableRadical r)
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hG : IsConnectedReductive G) : IsTorus R ∧ IsCentral r := by
  let b := toAlgebraicClosure k
  have hGbar := hG.baseChange_toAlgebraicClosure
  have hGbarPseudo : IsPseudoReductive ((GroupScheme.baseChange b).obj G) :=
    { smooth := hGbar.smooth
      isAffineHom := hGbar.isAffineHom
      connectedSpace := hGbar.connectedSpace
      hasTrivialUnipotentRadical := hG.hasTrivialGeometricUnipotentRadical }
  obtain ⟨hRbarTorus, hRbarCentral⟩ :=
    htorus (AlgebraicClosure k) _ hGbarPseudo _ _ hr.2.isClosedSubgroup hr.2.smooth
      hr.2.connectedSpace hr.2.isSolvableGroupScheme hr.2.isNormal
  obtain ⟨hsurj, hflat, -⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  have : Surjective b := hsurj
  have : Flat b := hflat
  exact ⟨IsTorus.of_baseChange (K := AlgebraicClosure k) hRbarTorus,
    IsCentral.of_baseChange b hRbarCentral⟩

/-- The three structural radical prerequisites imply the full central-torus
semisimple-quotient target, including existence of the torus. -/
def ReductiveCentralTorusSemisimpleQuotientFromStructureStatement : Prop :=
  SolvableRadicalExistenceStatement.{u} →
    AlgClosedReductiveNormalSolvableTorusStatement.{u} →
    ReductiveLargestCentralSubtorusBaseChangeStatement.{u} →
    ReductiveCentralTorusSemisimpleQuotientStatement.{u}

/-- Construct the radical as a central torus and prove semisimplicity for
every actual affine fppf quotient by it. -/
theorem reductiveCentralTorusSemisimpleQuotient_of_structure :
    ReductiveCentralTorusSemisimpleQuotientFromStructureStatement.{u} := by
  intro hexists htorus hbase k _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨R, r, hr⟩ :=
    reductiveGeometricSolvableRadicalExists_of_structure hexists htorus hbase k G hG
  obtain ⟨hRTorus, hRCentral⟩ := hr.isTorus_and_isCentral_of_structural htorus hG
  have : IsClosedImmersion r.hom.hom.left := hr.1.isClosedSubgroup
  have : IsAffineHom R.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  have : Smooth R.X.hom := hr.1.smooth
  let Z : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { toGrp := R, comm := hRTorus.isCommMonObj }
  refine ⟨Z, r, inferInstance, inferInstance, hRTorus, hr.1.isClosedSubgroup,
    hRCentral, ?_⟩
  intro Q q hq ha hft
  have : IsAffineHom Q.X.hom := ha
  exact hr.isSemisimple_quotient q hq

end Structure

end Langlands.GroupScheme
