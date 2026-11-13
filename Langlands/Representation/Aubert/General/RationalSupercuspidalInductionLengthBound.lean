import Langlands.Representation.Aubert.General.RationalAssociatedJacquetBudget
import Langlands.Representation.Aubert.General.RationalFullIntersectionBudget
import Langlands.Representation.Aubert.General.RationalSupercuspidalInductionInputsProof
import Langlands.Representation.Aubert.General.RationalIrreducibleJacquetFactorDetection
import Langlands.Representation.Aubert.General.RationalCuspidalExtractionInputs

/-! # The actual induction length bound from associated Jacquet detection -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands

/-- An actual representation equivalence transports a bounded composition
series across independent carrier universes, via the bounded-chain criterion. -/
theorem hasCompositionLengthAtMost_of_equiv.{uK, uG, uV, uW}
    {K : Type uK} [Field K] {H : Type uG} [Monoid H]
    {A : Rep.{uV} K H} {B : Rep.{uW} K H}
    (e : A.ρ.Equiv B.ρ) {b : ℕ} (hB : HasCompositionLengthAtMost B b) :
    HasCompositionLengthAtMost A b := by
  obtain ⟨n, hn, hs⟩ := hB
  let E : Subrepresentation A.ρ ≃o Subrepresentation B.ρ :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := A.ρ)).trans
      ((Submodule.orderIsoMapComap (repAsModuleEquiv e)).trans
        (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := B.ρ)).symm)
  apply LengthCriterionProof.hasCompositionLengthAtMost_of_bound
  intro m c hc
  exact (LengthCriterionProof.le_of_hasCompositionSeriesLength hs
    (fun q => E (c q)) (E.strictMono.comp hc)).trans hn

namespace Aubert.General.RationalPointFamily

universe u v

open Classical GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)

local instance rationalSupercuspidalLengthBoundPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) C)
  (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hRoots : HasRelativeRootSystem i)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

include hIdent hLength hRoots in
/-- Associated nonzero Jacquet detection gives the exact source-coset bound
on actual supercuspidal induction, in the original carrier universe. -/
theorem pointSupercuspidalInduction_compositionLengthAtMost_sourceCosets
    (hdet : RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v})
    (I : Finset (SimpleRoot i ν))
    (σ : SmoothRep.{0, u, v} ℂ (levi i ν I))
    (hσ : σ.IsIrreducible)
    (hcusp : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      hU I (hM I)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ) :
    HasCompositionLengthAtMost
      ((normalizedInductionFunctor.{u, v}
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
        (hU I)).obj σ).obj
      (Nat.card (standardLeviTransporterSourceCosets i ν I)) := by
  let h := isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
  let hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν
  let σ' := SmoothRep.universeLift.{u + 1} σ
  have hσ' : σ'.IsIrreducible := (SmoothRep.isIrreducible_universeLift_iff σ).mpr hσ
  have hcusp' : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      hU I (hM I) (hL I) σ' := by
    let := (hM I).locallyCompactSpace
    exact IsCuspidalFor.of_surjective_intertwiner hcusp
      (SmoothRep.universeLiftEquiv.{u + 1} σ).toIntertwiningMap
      (SmoothRep.universeLiftEquiv.{u + 1} σ).surjective
  have hcuspC := (isCorollaryLeviCuspidal_iff_isLeviCuspidal.{u, u, max (u + 1) v}
    I (hM I) (hL I) σ').mpr hcusp'
  let A := (normalizedInductionFunctor.{u, max (u + 1) v} (h I) (hU I)).obj σ'
  let Idx := {J : Finset (SimpleRoot i ν) // ∃ n, rootAssociation i ν hN hZ I J n}
  let F : ∀ J : Idx, SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X) ⥤
      SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J.1) :=
    fun J => jacquetFunctor (h J.1) (hU J.1)
  have hF : ∀ J, Derivative.Mirabolic.MapsShortExactIntertwiners (F J) := by
    intro J B D E f g hf hg hex
    have hs := jacquetFunctor_map_isShortExact (h J.1) (hU J.1)
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν J.1) f g ⟨hf, hg, hex⟩
    exact ⟨hs.1, hs.2.2, hs.2.1⟩
  let b : Idx → ℕ := fun J => (fullIntersectionRepresentatives cs J.1 I).card
  have hb : ∀ J, repLength ((F J).obj A).representation ≤ (b J : ℕ∞) := by
    intro J
    obtain ⟨n, hn⟩ := J.2
    exact (pointInducedJacquet_repLength_eq_fullIntersectionCount.{u, v}
      i ν hN hZ cs hIdent hLength hStandard hInter hRoots hG hi hν hM hU I J.1
      (rootAssociation_card_eq i ν hN hZ hn) σ' hσ' hcuspC).le
  have hrefl : rootAssociation i ν hN hZ I I 1 := rootAssociation_one i ν hN hZ I
  have hAlg := isInSupportCategory_cuspidalInduction.{_, u, max (u + 1) v}
    (h := h) (hU := hU) (hM := hM I) (hI := hL I) hrefl σ' hσ' hcusp'
  have hdetect : ∀ D : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X),
      D.IsIrreducible → SmoothRep.IsSubquotient D A → ∃ J, Nontrivial ((F J).obj D) := by
    intro D hD hDA
    obtain ⟨J, n, hassoc, -, hnt⟩ :=
      hdet k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM I D hD
        (hAlg.of_isSubquotient hDA)
    exact ⟨⟨J, n, hassoc⟩, hnt⟩
  have hsum : (∑ J, b J) ≤ Nat.card (standardLeviTransporterSourceCosets i ν I) := by
    have hcard : ∀ J : Idx, J.1.card = I.card := by
      rintro ⟨J, n, hn⟩
      exact (rootAssociation_card_eq i ν hN hZ hn).symm
    have hSimple := positiveSimpleReflectionComparison_of_rootLength
      i ν hN hZ cs hi.isSplitSubtorus.1 hRoots hν hLength
    exact (sum_card_fullIntersectionRepresentatives_le cs I
      (fun J : Idx => J.1) Subtype.val_injective hcard).trans
      (card_fullIntersectionPairs_le_sourceCosets
        i ν hN hZ cs hLength hSimple hG hi hν hStandard hIdent I)
  obtain ⟨m, hm, s, hs⟩ :=
    exactFamilyLengthBound Idx (RationalPoint k G.X) (fun J => levi i ν J.1) F hF A b hb hdetect
  have hA : HasCompositionLengthAtMost A.obj
      (Nat.card (standardLeviTransporterSourceCosets i ν I)) :=
    ⟨m, hm.trans hsum, s, hs⟩
  exact hasCompositionLengthAtMost_of_equiv
    (normalizedInductionUniverseLiftEquiv.{u, v, u + 1} (h I) (hU I) σ) hA

/-- Choose the actual composition series in the original carrier universe,
with its length bounded by the literal source-coset count. -/
def pointSupercuspidalInductionCompositionSeriesOfDetection
    (hdet : RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v})
    (I : Finset (SimpleRoot i ν))
    (σ : SmoothRep.{0, u, v} ℂ (levi i ν I))
    (hσ : σ.IsIrreducible)
    (hcusp : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      hU I (hM I)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ) :
    Σ n : Fin (Nat.card (standardLeviTransporterSourceCosets i ν I) + 1),
      {s : ObjectRepFiltration
        ((normalizedInductionFunctor.{u, v}
          (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
          (hU I)).obj σ).obj n.val // s.HasSimpleFactors} := by
  let H := pointSupercuspidalInduction_compositionLengthAtMost_sourceCosets.{u, v}
    i ν hN hZ cs hIdent hLength hStandard hInter hRoots hG hi hν hM hU hdet I σ hσ hcusp
  let n := Classical.choose H
  have hn : n ≤ Nat.card (standardLeviTransporterSourceCosets i ν I) :=
    (Classical.choose_spec H).1
  let hs := (Classical.choose_spec H).2
  exact ⟨⟨n, Nat.lt_succ_of_le hn⟩, Classical.choose hs, Classical.choose_spec hs⟩

end Aubert.General.RationalPointFamily

end Langlands
