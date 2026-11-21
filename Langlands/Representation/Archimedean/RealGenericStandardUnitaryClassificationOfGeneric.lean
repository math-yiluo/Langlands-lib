import Langlands.Global.RankinSelberg.RealStandardIntertwinerPairLReduction
import Langlands.Representation.Archimedean.RealGenericStandardUnitaryClassificationStatement
import Langlands.Representation.Archimedean.RealGLTwoPrincipalSeriesUnitaryBound
import Langlands.Representation.Archimedean.RealRankFourUnitaryBound
import Langlands.Representation.Archimedean.RealStandardEllipticCartanComparisonProof
import Langlands.Representation.Archimedean.RealStandardEllipticCartanReduction
import Langlands.Representation.Archimedean.RealStandardFactorUnitarity
import Langlands.Representation.Archimedean.RealStandardHermitianPairDecomposition
import Langlands.Representation.Archimedean.RealStandardParameterUnitary
import Langlands.Representation.Archimedean.RealStandardUnlinkedNecessity

/-! # The real generic unitary classification on irreducible generic standard modules -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

/-- `RealGenericStandardUnitaryClassificationStatement` with the additional hypothesis that
the irreducible infinitesimally unitary standard module is generic. -/
def RealGenericStandardUnitaryClassificationOfGenericStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) →
    IsRealGenericGKModule n (realStandardLie n ds) →
    IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds) →
    ∃ es : List RealBlock, IsRealGenericUnitaryInducingData es ∧
      HasRealStandardParameter n (realStandardRep n ds) (realStandardLie n ds) es

/-- A unitary character twisted by `±α` gives a unitarizable principal series of `GL₂(ℝ)`
only for `α < 1/2`. -/
private theorem character_pair_bound (c : RealCharacterData) {α : ℝ}
    (hU : IsRealUnitarizableGKModule (realRank
        [realBlockTwist α (.character c), realBlockTwist (-α) (.character c)])
      (realStandardRep (realRank
        [realBlockTwist α (.character c), realBlockTwist (-α) (.character c)])
        [realBlockTwist α (.character c), realBlockTwist (-α) (.character c)])
      (realStandardLie (realRank
        [realBlockTwist α (.character c), realBlockTwist (-α) (.character c)])
        [realBlockTwist α (.character c), realBlockTwist (-α) (.character c)])) :
    α < 1 / 2 := by
  have h := (RealGLTwoPrincipalSeriesUnitaryBound.exponent_difference
    (RealJacquetFrobenius.charData c.parity (c.exponent + α))
    (RealJacquetFrobenius.charData c.parity (c.exponent + ((-α : ℝ) : ℂ))) hU).1
  have hre : ((RealJacquetFrobenius.charData c.parity (c.exponent + α)).exponent -
      (RealJacquetFrobenius.charData c.parity (c.exponent + ((-α : ℝ) : ℂ))).exponent).re =
      2 * α := by
    change (c.exponent + α - (c.exponent + ((-α : ℝ) : ℂ))).re = 2 * α
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
    ring
  rw [hre] at h
  linarith [le_abs_self (2 * α)]

/-- A unitary discrete-series block twisted by `±α` gives a unitarizable unlinked rank-four
standard module only for `α < 1/2`. -/
private theorem induced_pair_bound (d : ComplexCharacterData) (hd : 0 < d.weight) {α : ℝ}
    (hu : AreRealBlocksUnlinked (realBlockTwist α (.induced d))
      (realBlockTwist (-α) (.induced d)))
    (hU : IsRealUnitarizableGKModule (realRank
        [realBlockTwist α (.induced d), realBlockTwist (-α) (.induced d)])
      (realStandardRep (realRank
        [realBlockTwist α (.induced d), realBlockTwist (-α) (.induced d)])
        [realBlockTwist α (.induced d), realBlockTwist (-α) (.induced d)])
      (realStandardLie (realRank
        [realBlockTwist α (.induced d), realBlockTwist (-α) (.induced d)])
        [realBlockTwist α (.induced d), realBlockTwist (-α) (.induced d)])) :
    α < 1 / 2 := by
  have he : (characterOfParams d.weight (d.exponent + ((-α : ℝ) : ℂ))).exponent =
      d.exponent - (α : ℂ) := by
    rw [characterOfParams_exponent, Complex.ofReal_neg, sub_eq_add_neg]
  have h := realRankFourUnitaryBound (characterOfParams d.weight (d.exponent + α))
    (characterOfParams d.weight (d.exponent + ((-α : ℝ) : ℂ))) hd.ne' rfl d.exponent α rfl he
    hu hU
  linarith [le_abs_self α]

private theorem pair_bound {δ : RealBlock} (hδ : IsRealUnitaryDiscreteBlock δ) {α : ℝ}
    (hu : [realBlockTwist α δ, realBlockTwist (-α) δ].Pairwise AreRealBlocksUnlinked)
    (hU : IsRealUnitarizableGKModule (realRank [realBlockTwist α δ, realBlockTwist (-α) δ])
      (realStandardRep (realRank [realBlockTwist α δ, realBlockTwist (-α) δ])
        [realBlockTwist α δ, realBlockTwist (-α) δ])
      (realStandardLie (realRank [realBlockTwist α δ, realBlockTwist (-α) δ])
        [realBlockTwist α δ, realBlockTwist (-α) δ])) :
    α < 1 / 2 := by
  cases δ with
  | character c => exact character_pair_bound c hU
  | induced d => exact induced_pair_bound d hδ.2 (List.pairwise_pair.1 hu) hU

/-- The pair bound turns a Hermitian inducing factor into a generic unitary inducing
factor. -/
private theorem genericFactor_of_hermitian {A : List RealBlock}
    (hA : IsRealHermitianInducingFactor A) (hu : A.Pairwise AreRealBlocksUnlinked)
    (hU : IsRealUnitarizableGKModule (realRank A) (realStandardRep (realRank A) A)
      (realStandardLie (realRank A) A)) :
    IsRealGenericUnitaryInducingFactor A := by
  obtain ⟨δ, hδ, hsingle | ⟨α, hα, rfl⟩⟩ := hA
  · exact ⟨δ, hδ, Or.inl hsingle⟩
  · exact ⟨δ, hδ, Or.inr ⟨α, hα, pair_bound hδ hu hU, rfl⟩⟩

theorem realGenericStandardUnitaryClassification_of_generic :
    RealGenericStandardUnitaryClassificationOfGenericStatement := by
  intro n ds hrank hirr hgen hunit
  have hunique : RealPositiveWeightStandardUniqueStatement :=
    realStandardEllipticCartanReduction
      RealStandardEllipticCartan.realStandardEllipticCartanComparison
  -- Normalize: split weight-zero blocks and make all weights positive.
  let fs := ds.flatMap realBlockNormalize
  have hfRank : realRank fs = n := (realRank_flatMap_normalize ds).trans hrank
  have hF : RealInjectiveIntertwinerExists n fs ds :=
    (RealInjectiveIntertwinerExists.refl n ds).of_eq
      (realStandardModule_flatMap_normalize n ds).symm rfl
  obtain ⟨-, hfI, hfG, hfU⟩ := realStandardParameter_model hirr hgen hunit
    (⟨hfRank, hF⟩ : HasRealStandardParameter n (realStandardRep n ds) (realStandardLie n ds) fs)
  have hfpos : ∀ d : ComplexCharacterData, .induced d ∈ fs → 0 < d.weight :=
    fun _ => weight_pos_of_mem_flatMap_normalize
  -- Group the normalized blocks into Hermitian inducing factors.
  obtain ⟨factors, hperm, hfac⟩ :=
    realStandardHermitianPairDecomposition hunique n fs hfRank hfpos hfI hfG hfU
  have hfUnl : fs.Pairwise AreRealBlocksUnlinked :=
    (List.pairwise_flatMap.1
      (realStandard_moeglinUnlinked_of_unitaryGeneric n fs hfRank hfI hfG hfU)).2
  let es := factors.flatten
  have heUnl : es.Pairwise AreRealBlocksUnlinked := hperm.symm.pairwise hfUnl AreRealBlocksUnlinked.symm
  have heRank : realRank es = n := (realRank_perm hperm).trans hfRank
  have hE : RealInjectiveIntertwinerExists n es ds :=
    (realUnlinkedStandardPermutation n es fs heRank heUnl hperm).trans hF
  have heParam : HasRealStandardParameter n (realStandardRep n ds) (realStandardLie n ds) es :=
    ⟨heRank, hE⟩
  obtain ⟨-, heI, -, heU⟩ := realStandardParameter_model hirr hgen hunit heParam
  -- Each factor is pairwise unlinked and irreducible.
  have hpairs : ∀ A ∈ factors, A.Pairwise AreRealBlocksUnlinked :=
    (List.pairwise_flatten.1 heUnl).1
  have hirrs : ∀ A ∈ factors,
      IsIrreducibleGKModule (realStandardRep (realRank A) A) (realStandardLie (realRank A) A) := by
    intro A hA
    obtain ⟨s, t, hst⟩ := List.mem_iff_append.1 hA
    have hes : es = s.flatten ++ A ++ t.flatten := by
      simp only [es, hst, List.flatten_append, List.flatten_cons, List.append_assoc]
    rw [hes] at heRank heI
    exact realStandardIrreducibilityInStages n s.flatten A t.flatten heRank heI
  -- Each factor is unitarizable.
  have hunits := realStandardFactorUnitarity factors n heRank
    (fun A hA => realHermitianInducingFactor_dualEquiv A (hfac A hA) (hpairs A hA) (hirrs A hA))
    heI heU
  exact ⟨es, ⟨factors, rfl, fun A hA =>
    genericFactor_of_hermitian (hfac A hA) (hpairs A hA) (hunits A hA)⟩, heParam⟩

end Langlands.Archimedean
