import Langlands.GroupScheme.Rational.FiniteFieldCentralCocharacterSolvableStatement
import Langlands.GroupScheme.Rational.FiniteFieldQuasiSplitStatement
import Langlands.GroupScheme.Rational.CentralCocharacterReduction
import Langlands.GroupScheme.Rational.SplitUnipotentQuotientHomLift
import Langlands.GroupScheme.Dynamic.CentralQuotient
import Langlands.GroupScheme.Absolute.SolvableQuotientExtension
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Reductive.PerfectFieldProof

/-! # Reduction of finite-field solvability to three structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- An actual reductive quotient by the ground-field unipotent radical, with
centrality of every cocharacter over the unchanged ground field. -/
structure CentralCocharacterReductiveQuotientData
    (G : GroupScheme (Spec (CommRingCat.of k))) where
  radical : GroupScheme (Spec (CommRingCat.of k))
  radicalInclusion : radical ⟶ G
  isUnipotentRadical : IsUnipotentRadical radicalInclusion
  quotient : GroupScheme (Spec (CommRingCat.of k))
  projection : G ⟶ quotient
  isFppfQuotient :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range radicalInclusion) projection
  isConnectedReductive : IsConnectedReductive quotient
  central_cocharacters :
    ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ quotient,
      Dynamic.centralizer χ = ⊤

variable [PerfectField k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- Lifting cocharacters through the radical quotient and descending centrality
produce a reductive quotient with only central ground-field cocharacters. -/
theorem nonempty_centralCocharacterReductiveQuotientData
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hcentral : ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      Dynamic.centralizer χ = ⊤) :
    Nonempty (CentralCocharacterReductiveQuotientData G) := by
  obtain ⟨U, i, hi⟩ := unipotentRadicalExistence k G
  obtain ⟨Q, q, hq, hQ⟩ := unipotentRadicalQuotient k G U i hi
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Smooth U.X.hom := hi.smooth
  have : ConnectedSpace U.X.left := hi.connectedSpace
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsAffineHom Q.X.hom := hQ.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : QuasiCompact q.hom.hom.left := inferInstance
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have hcentralQ :
      ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Q,
        Dynamic.centralizer χ = ⊤ :=
    Dynamic.central_cocharacters_of_fpqc_of_lifts q
      (exists_cocharacter_lift_of_perfectField_unipotent_kernel
        i q hq hi.isUnipotent hstable) hcentral
  exact ⟨⟨U, i, hi, Q, q, hq,
    (perfectFieldPseudoReductive k Q).mp hQ, hcentralQ⟩⟩

/-- A chosen actual reductive radical quotient with central cocharacters.
Stable-vector existence remains an explicit input to the construction. -/
def centralCocharacterReductiveQuotient
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hcentral : ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      Dynamic.centralizer χ = ⊤) :
    CentralCocharacterReductiveQuotientData G :=
  Classical.choice (nonempty_centralCocharacterReductiveQuotientData G hstable hcentral)

namespace CentralCocharacterReductiveQuotientData

omit [PerfectField k] [Smooth G.X.hom] [ConnectedSpace G.X.left] in
/-- If the reductive quotient is quasi-split, the parabolic comparison makes
its Borel inclusion an isomorphism, and solvability extends across the radical. -/
theorem isSolvableGroupScheme
    (D : CentralCocharacterReductiveQuotientData G)
    (hdynamic : ParabolicDynamicStatement.{u})
    (hquasi : IsQuasiSplit D.quotient) : IsSolvableGroupScheme G := by
  have : IsClosedImmersion D.radicalInclusion.hom.hom.left :=
    D.isUnipotentRadical.isClosedSubgroup
  have : Smooth D.radical.X.hom := D.isUnipotentRadical.smooth
  have : IsAffineHom D.radical.X.hom := by
    rw [← Over.w D.radicalInclusion.hom.hom]
    infer_instance
  exact isSolvableGroupScheme_of_unipotent_fppfQuotient
    D.isUnipotentRadical.isUnipotent D.isFppfQuotient
    (hquasi.isSolvableGroupScheme_of_central_cocharacters hdynamic D.central_cocharacters)

end CentralCocharacterReductiveQuotientData

/-- The finite-field target follows from stable-vector existence, the dynamic
description of parabolics, and finite-field quasi-splitness. -/
theorem finiteFieldCentralCocharacterSolvable_of
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hdynamic : ParabolicDynamicStatement.{u})
    (hquasi : FiniteFieldQuasiSplitStatement.{u}) :
    FiniteFieldCentralCocharacterSolvableStatement.{u} := by
  intro k _ _ G _ _ _ hcentral
  let D := centralCocharacterReductiveQuotient G hstable hcentral
  exact D.isSolvableGroupScheme G hdynamic (hquasi k D.quotient D.isConnectedReductive)

end Langlands.GroupScheme
