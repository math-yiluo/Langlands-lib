import Langlands.Representation.Aubert.General.RationalRankOneJacquetReduction
import Langlands.Representation.Aubert.General.RationalRankOneGeometricJacquetProof
import Langlands.Representation.Aubert.General.RationalRankOneLengthInputsProof
import Langlands.Representation.Aubert.General.RationalMaximalCuspidalDetectionProof
import Langlands.Representation.Aubert.General.RankOneJacquetSupportDeduction

/-! # The rational rank-one Jacquet pattern from maximal Jacquet detection -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- Detection of every irreducible subquotient of a maximal cuspidal induction
by a maximal proper standard Jacquet module implies the exact rational rank-one
Jacquet target. -/
def RationalRankOneJacquetModulesFromDetectionStatement : Prop :=
  RationalMaximalCuspidalJacquetDetectionStatement.{u, v} →
    RationalRankOneJacquetModulesStatement.{u, v}

/-- Maximal Jacquet detection, together with the published geometric
computation `rationalRankOneGeometricJacquet`, proves the exact rational
rank-one Jacquet target. -/
theorem rationalRankOneJacquetModules_of_maximalDetection
    (hdet : RationalMaximalCuspidalJacquetDetectionStatement.{u, v}) :
    RationalRankOneJacquetModulesStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  intro _ hN hZ C actual hLength hSimple hIdent hMin hAssoc J hJ σ hσ hcusp hred n hn hself
  let h := isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
  have hUc : ∀ K, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν K) :=
    standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν
  obtain ⟨hgeometry, hvanish⟩ :=
    rationalRankOneGeometricJacquet k G hG T i hi ν hν hStandard hInter hRoots hU hM
      hN hZ C actual hLength hSimple hIdent hMin hAssoc J hJ σ.val hcusp n hn hself
  have hdetJ := hdet k G hG T i hi ν hν hStandard hInter hRoots hU hM J hJ σ.val hσ hcusp
  obtain ⟨α, rfl⟩ := hJ
  -- Every irreducible subquotient has a nonzero Jacquet module along `J` itself.
  have hfix : ∀ D : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X),
      D.IsIrreducible →
      IsSubquotient D ((normalizedInductionFunctor.{u, max (u + 1) v}
        (h (Finset.univ.erase α)) (hU (Finset.univ.erase α))).obj σ.val) →
      Nontrivial ((jacquetFunctor.{u, max (u + 1) v}
        (h (Finset.univ.erase α)) (hU (Finset.univ.erase α))).obj D) := by
    intro D hD hDsub
    obtain ⟨β, hβ⟩ := hdetJ D hD hDsub
    by_cases hβα : β = α
    · subst hβα
      exact hβ
    · exfalso
      have hne : Finset.univ.erase β ≠ Finset.univ.erase α := fun heq =>
        hβα ((Finset.erase_inj Finset.univ (Finset.mem_univ β)).mp heq)
      have hz := (SmoothRep.isZero_iff_subsingleton_carrier _).mp
        (hvanish _ (IsMaximalStandard.ne_univ ⟨β, rfl⟩) hne)
      exact not_subsingleton_iff_nontrivial.mpr hβ
        (jacquet_subsingleton_of_isSubquotient (h _) (hU _) (hUc _) hDsub hz)
  -- The maximal Jacquet lengths of the induction add up to two.
  have hτ : ((conjugationFunctor ((n : RationalPoint k G.X))⁻¹
      (fun x => by simpa using hself x)).obj σ.val).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff σ.val.representation
      (conjugationEquiv ((n : RationalPoint k G.X))⁻¹
        (fun x => by simpa using hself x))).mpr hσ
  have hbud : (∑ β : SimpleRoot i ν,
      repLength ((jacquetFunctor.{u, max (u + 1) v}
        (h (Finset.univ.erase β)) (hU (Finset.univ.erase β))).obj
        ((normalizedInductionFunctor.{u, max (u + 1) v}
          (h (Finset.univ.erase α)) (hU (Finset.univ.erase α))).obj σ.val)).representation)
        ≤ 2 := by
    rw [Finset.sum_eq_single α]
    · obtain ⟨f, g, hf, hg, hfg⟩ := hgeometry
      rw [repLength_eq_add_of_exact f g hf hg hfg, repLength_eq_one_iff.mpr hτ,
        repLength_eq_one_iff.mpr hσ]
      norm_num
    · intro β _ hβα
      have hne : Finset.univ.erase β ≠ Finset.univ.erase α := fun heq =>
        hβα ((Finset.erase_inj Finset.univ (Finset.mem_univ β)).mp heq)
      rw [repLength_eq_zero_iff.mpr ((SmoothRep.isZero_iff_subsingleton_carrier _).mp
        (hvanish _ (IsMaximalStandard.ne_univ ⟨β, rfl⟩) hne))]
    · intro hα
      exact absurd (Finset.mem_univ α) hα
  -- Length two of the induction.
  let : σ.val.representation.IsIrreducible := hσ
  have : Nontrivial σ.val :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi i ν (Finset.univ.erase α)))
      σ.val.representation.asModule
  have : Nontrivial ((normalizedInductionFunctor.{u, max (u + 1) v}
      (h (Finset.univ.erase α)) (hU (Finset.univ.erase α))).obj σ.val) :=
    rationalStandardInductionNonzero k G hG T i hi ν hν hStandard (Finset.univ.erase α)
      (hU (Finset.univ.erase α)) σ.val
  have hlen := repLength_le_two_of_jacquetFamily
    (P := fun β : SimpleRoot i ν => parabolic i ν (Finset.univ.erase β))
    (M := fun β : SimpleRoot i ν => levi i ν (Finset.univ.erase β))
    (U := fun β : SimpleRoot i ν => unipotent i ν (Finset.univ.erase β))
    (fun β => h (Finset.univ.erase β)) (fun β => hU (Finset.univ.erase β))
    (fun β => hUc (Finset.univ.erase β))
    ((normalizedInductionFunctor.{u, max (u + 1) v}
      (h (Finset.univ.erase α)) (hU (Finset.univ.erase α))).obj σ.val)
    hbud (fun D hD hDsub => hdetJ D hD hDsub)
  obtain ⟨A, B, hseries⟩ := exists_hasTwoConstituents_of_length_le_two _ hlen hred
  -- Both constituents have nonzero Jacquet modules along `J`.
  have hsub := hseries.isSubquotient
  exact exists_rankOneJacquetPattern_of_exact_data
    (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν) (h := h) (hU := hU)
    (T := torusPoints i) hUc (Finset.univ.erase α) σ.val hσ n hself A B hseries
    (hfix A.val hseries.1 hsub.1) (hfix B.val hseries.2.1 hsub.2) hgeometry hvanish

/-- The named implication holds. -/
theorem rationalRankOneJacquetModulesFromDetection :
    RationalRankOneJacquetModulesFromDetectionStatement.{u, v} :=
  rationalRankOneJacquetModules_of_maximalDetection

/-- Actual rational cuspidal Jacquet-factor extraction proves the exact
rational rank-one Jacquet target. -/
theorem rationalRankOneJacquetModules_of_extraction
    (hextract : RationalCuspidalJacquetFactorExtractionStatement.{u, v}) :
    RationalRankOneJacquetModulesStatement.{u, v} :=
  rationalRankOneJacquetModules_of_maximalDetection
    (rationalMaximalCuspidalJacquetDetectionFromExtraction hextract)

end Langlands.Aubert.General.RationalPointFamily
