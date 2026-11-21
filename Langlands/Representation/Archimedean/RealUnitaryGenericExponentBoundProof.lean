import Langlands.Global.RankinSelberg.RealStandardIntertwinerPairLReduction
import Langlands.Representation.Archimedean.RealGLTwoPrincipalSeriesUnitaryBound
import Langlands.Representation.Archimedean.RealRankFourUnitaryBound
import Langlands.Representation.Archimedean.RealStandardEllipticCartanComparisonProof
import Langlands.Representation.Archimedean.RealStandardFactorUnitarity
import Langlands.Representation.Archimedean.RealStandardHermitianPairDecomposition
import Langlands.Representation.Archimedean.RealStandardUnlinkedNecessity

/-! # The strict exponent bound for real unitary generic standard parameters -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.RealLocalJacquet

universe uV

private theorem unitary_inducing_factor {A : List RealBlock}
    (hA : IsRealHermitianInducingFactor A) (hu : A.Pairwise AreRealBlocksUnlinked)
    (hunit : IsRealUnitarizableGKModule (realRank A)
      (realStandardRep (realRank A) A) (realStandardLie (realRank A) A)) :
    IsRealGenericUnitaryInducingFactor A := by
  obtain ⟨δ, hδ, rfl | ⟨a, ha, rfl⟩⟩ := hA
  · exact ⟨δ, hδ, Or.inl rfl⟩
  refine ⟨δ, hδ, Or.inr ⟨a, ha, ?_, rfl⟩⟩
  cases δ with
  | character c =>
    let cPos := RealJacquetFrobenius.charData c.parity (c.exponent + (a : ℂ))
    let cNeg := RealJacquetFrobenius.charData c.parity (c.exponent + ((-a : ℝ) : ℂ))
    have hdiff : (cPos.exponent - cNeg.exponent).re = 2 * a := by
      change (c.exponent + (a : ℂ) - (c.exponent + ((-a : ℝ) : ℂ))).re = 2 * a
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
      ring
    have hb := (RealGLTwoPrincipalSeriesUnitaryBound.exponent_difference cPos cNeg hunit).1
    rw [hdiff, abs_of_pos (by positivity : 0 < 2 * a)] at hb
    linarith
  | induced d =>
    let dPos := characterOfParams d.weight (d.exponent + (a : ℂ))
    let dNeg := characterOfParams d.weight (d.exponent + ((-a : ℝ) : ℂ))
    have hneg : dNeg.exponent = d.exponent - (a : ℂ) := by
      simp only [dNeg, characterOfParams, Complex.ofReal_neg, sub_eq_add_neg]
    have hUnlinked : AreRealBlocksUnlinked (.induced dPos) (.induced dNeg) :=
      (List.pairwise_cons.mp hu).1 _ List.mem_cons_self
    have hb := realRankFourUnitaryBound dPos dNeg (ne_of_gt hδ.2) rfl
      d.exponent a rfl hneg hUnlinked hunit
    simpa only [abs_of_pos ha] using hb

private theorem normalized_exponent_rep (x : RealBlock) :
    ∃ y ∈ realBlockNormalize x, realBlockExponent y = realBlockExponent x := by
  have hexpand : ∃ y, y ∈ realBlockExpand x := by
    cases x with
    | character c => exact ⟨.character c, by simp [realBlockExpand]⟩
    | induced d => by_cases h : d.weight = 0 <;> simp [realBlockExpand, h]
  obtain ⟨y, hy⟩ := hexpand
  refine ⟨y.positiveWeight, List.mem_map_of_mem hy, ?_⟩
  rw [← realBlockExponent_of_mem_expand hy]
  cases y with
  | character _ => rfl
  | induced d =>
    by_cases h : d.weight < 0 <;>
      simp [RealBlock.positiveWeight, h, realBlockExponent, ComplexCharacterData.conj]

private theorem realStandard_exponent_bound_of_hermitian_factors
    (hunique : RealPositiveWeightStandardUniqueStatement)
    (n : ℕ) (ds : List RealBlock) (hrank : realRank ds = n)
    (hirr : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds))
    (hgen : IsRealGenericGKModule n (realStandardLie n ds))
    (hunit : IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds)) :
    ∀ x ∈ ds, |realBlockExponent x| < 1 / 2 := by
  let es := ds.flatMap realBlockNormalize
  have heParam : HasRealStandardParameter n (realStandardRep n ds) (realStandardLie n ds) es :=
    ⟨(realRank_flatMap_normalize ds).trans hrank,
      (RealInjectiveIntertwinerExists.refl n ds).of_eq
        (realStandardModule_flatMap_normalize n ds).symm rfl⟩
  obtain ⟨herank, heirr, hegen, heunit⟩ := realStandardParameter_model hirr hgen hunit heParam
  have heUnlinked := realStandard_moeglinUnlinked_of_unitaryGeneric n es herank heirr hegen heunit
  unfold IsRealMoeglinUnlinked realMoeglinData at heUnlinked
  rw [List.pairwise_flatMap] at heUnlinked
  have hePairwise : es.Pairwise AreRealBlocksUnlinked := heUnlinked.2
  obtain ⟨groups, hperm, hfac⟩ := realStandardHermitianPairDecomposition hunique n es herank
    (fun _ => weight_pos_of_mem_flatMap_normalize) heirr hegen heunit
  have hRankGroups := (realRank_perm hperm).trans herank
  have hPairwiseGroups := hperm.symm.pairwise hePairwise (fun h => h.symm)
  have hGroupParam :
      HasRealStandardParameter n (realStandardRep n es) (realStandardLie n es) groups.flatten :=
    ⟨hRankGroups, realUnlinkedStandardPermutation n groups.flatten es hRankGroups
      hPairwiseGroups hperm⟩
  obtain ⟨hgrank, hgirr, _, hgunit⟩ :=
    realStandardParameter_model heirr hegen heunit hGroupParam
  have hLocal (A : List RealBlock) (hA : A ∈ groups) :
      A.Pairwise AreRealBlocksUnlinked ∧
      IsIrreducibleGKModule (realStandardRep (realRank A) A) (realStandardLie (realRank A) A) := by
    obtain ⟨pre, post, h⟩ := List.mem_iff_append.mp hA
    have hflat : groups.flatten = pre.flatten ++ A ++ post.flatten := by
      simp only [h, List.flatten_append, List.flatten_cons, List.append_assoc]
    have hinfix : A <:+: groups.flatten :=
      ⟨pre.flatten, post.flatten, by simpa only [List.append_assoc] using hflat.symm⟩
    exact ⟨hPairwiseGroups.sublist hinfix.sublist,
      realStandardIrreducibilityInStages n pre.flatten A post.flatten
        (hflat ▸ hgrank) (hflat ▸ hgirr)⟩
  have hHerm (A : List RealBlock) (hA : A ∈ groups) : HasRealStandardHermitianDualEquiv A :=
    realHermitianInducingFactor_dualEquiv A (hfac A hA) (hLocal A hA).1 (hLocal A hA).2
  have hGroupUnitaryData : IsRealGenericUnitaryInducingData groups.flatten := by
    refine ⟨groups, rfl, fun A hA => ?_⟩
    exact unitary_inducing_factor (hfac A hA) (hLocal A hA).1
      (realStandardFactorUnitarity groups n hgrank hHerm hgirr hgunit A hA)
  intro x hx
  obtain ⟨y, hy, he⟩ := normalized_exponent_rep x
  rw [← he]
  exact hGroupUnitaryData.exponent_bound (hperm.mem_iff.mpr (List.mem_flatMap.mpr ⟨x, hx, hy⟩))

/-- The real exponents of an infinitesimally unitary irreducible generic standard
parameter lie in the open interval `(-1/2, 1/2)`. -/
theorem realUnitaryGenericExponentBound : RealUnitaryGenericExponentBoundStatement.{uV} :=
  realUnitaryGenericExponentBound_of_standard
    (realStandard_exponent_bound_of_hermitian_factors
      (realStandardEllipticCartanReduction
        RealStandardEllipticCartan.realStandardEllipticCartanComparison))

end Langlands.Archimedean
