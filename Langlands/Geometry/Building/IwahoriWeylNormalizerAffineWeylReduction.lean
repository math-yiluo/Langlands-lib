import Langlands.Geometry.Building.IwahoriWeylExactSequenceReduction
import Langlands.Geometry.Building.IwahoriWeylChamberFromExactSequence
import Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductProof

/-!
# The Iwahori–Weyl exact sequence and chamber splitting from KP Theorem 7.5.3(2)

KP Theorem 7.8.1(1) (`IwahoriWeylExactSequenceStatement`) and KP 7.8.2
(`IwahoriWeylChamberSplittingStatement`) follow from the range part of KP Theorem 7.5.3(2)
(`SimplyConnectedNormalizerAffineWeylStatement`) alone. The other inputs of the published
assembly are supplied by published proofs: both normalities from
`ZeroSubgroupCommutatorNormality`, KP Fact 2.6.22 from `simplyConnectedCentralizerProduct`,
KP Corollary 2.6.28 from the cover-image comparison, and simple transitivity on chambers from
`affineChamberSimpleTransitivity`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- KP Corollary 2.6.28 for the data of `P`: `G(F)^0 ∩ Z(F)^1 = Z(F)^0`. -/
theorem centralizerZeroIntersection : P.zeroDatum.CentralizerZeroIntersectionStatement :=
  P.zeroDatum.centralizerZeroIntersection_of_coverImage
    P.zeroDatum.coverImageCentralizerNormKernel

/-- KP Theorem 7.8.1(1) for the data `P`, from the range part of KP Theorem 7.5.3(2). -/
theorem iwahoriWeylExactSequence_of_normalizerAffineWeyl
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hW : SimplyConnectedNormalizerAffineWeylStatement.{u}) :
    P.IwahoriWeylExactSequence := by
  have hN : P.normalizerZero.Normal := P.normal_normalizerZero
  have hG : P.zeroSubgroup.Normal := P.normal_zeroSubgroup
  exact ⟨hN, hG, P.exists_affinePart_equiv_of_action
      (P.normalizerAffineEquiv_mem_affineWeylGroup hP hW)
      (P.normalizerAffineEquiv_eq_one_iff P.centralizerZeroIntersection)
      (P.exists_normalizerZeroComponent_normalizerAffineEquiv_eq hP hW),
    P.toComponents_ker_eq_affinePart, P.toComponents_surjective simplyConnectedCentralizerProduct⟩

end ParahoricBuildingData

/-- KP Theorem 7.8.1(1) and KP 7.8.2 follow from the range part of KP Theorem 7.5.3(2):
if `N(F) ∩ G(F)^♮` acts on the apartment through exactly `W(Ψ)` for all actual building data,
then the Iwahori–Weyl exact sequence and the chamber splitting hold for all actual building
data under the apartment axioms. -/
def IwahoriWeylNormalizerAffineWeylReductionStatement : Prop :=
  SimplyConnectedNormalizerAffineWeylStatement.{u} →
    IwahoriWeylExactSequenceStatement.{u} ∧ IwahoriWeylChamberSplittingStatement.{u}

/-- The reduction holds: the exact sequence by the per-data assembly, and the chamber splitting
from the exact sequence by the published unconditional reduction. -/
theorem iwahoriWeylNormalizerAffineWeylReduction :
    IwahoriWeylNormalizerAffineWeylReductionStatement.{u} := by
  intro hW
  have hex : IwahoriWeylExactSequenceStatement.{u} := by
    intro F _ _ _ _ G _ P hP
    exact P.iwahoriWeylExactSequence_of_normalizerAffineWeyl hP hW
  exact ⟨hex, iwahoriWeylChamberExactSequenceReduction hex⟩

end Langlands.Geometry.Building
