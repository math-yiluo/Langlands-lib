import Langlands.Representation.Classification.SemistandardLanglandsStatement
import Langlands.Representation.Classification.WholeLeviLanglandsRecoveryProof
import Langlands.Group.GL.SemistandardStandardizationProof
import Langlands.Group.GL.DiagonalLevi
import Langlands.Representation.Exponents.PairConjugation
import Langlands.Representation.Induction.InnerLeviTransport
import Langlands.Representation.Twist.LeviRealPowerFaithfulnessProof

/-! Semistandard Langlands conjugacy by an actual permutation matrix. -/

noncomputable section

namespace Langlands

open GeneralLinear Exponents RelativeRegularComparison

universe uF uV uW uJ uK

/-- Equivalent irreducible quotients of semistandard and standard regular
tempered inductions recover the full datum under a permutation matrix. -/
theorem glSemistandardLanglandsConjugacy :
    GLSemistandardLanglandsConjugacyStatement.{uF, uV, uW, uJ, uK} := by
  intro p _ F T
  let := T.topology
  intro n hn A₀ P B hP σ τ hσ hσT hτ hτT t u ht hu J K hJ hK hqJ hqK hJK
  obtain ⟨w, m, hm⟩ := glSemistandardStandardization p F n P hP
  let e := T.innerLeviEquiv P.shape m
  let σ₀ := Rep.of (σ.ρ.comp e.toMulEquiv.symm.toMonoidHom)
  have hσ₀ : Representation.IsIrreducible σ₀.ρ :=
    (isIrreducible_iff_of_equiv (innerPullbackEquiv σ.ρ m)).mpr hσ
  have hσ₀T : IsLeviTempered T P.shape σ₀ :=
    (T.isLeviTempered_inner_iff P.shape m σ).mpr hσT
  obtain ⟨qJ, hqJ⟩ := hqJ
  let E := (T.innerLeviInducedEquiv P.shape m t σ.ρ).trans
    (T.conjugateParabolicInducedEquiv P (T.leviRealPowerTwist P.shape t σ.ρ))
  have hq₀ : ∃ q : (T.normalizedParabolicInduced P.shape
      (T.leviRealPowerTwist P.shape t σ₀.ρ)).IntertwiningMap J.ρ,
      Function.Surjective q :=
    ⟨qJ.comp E.toIntertwiningMap, hqJ.comp E.surjective⟩
  obtain ⟨hB, htu, hrep⟩ :=
    glWholeLeviLanglandsRecovery p F T n hn P.shape B σ₀ τ
      hσ₀ hσ₀T hτ hτT t u ht hu J K hJ hK hq₀ hqK hJK
  cases hB
  change t = u at htu
  subst u
  refine ⟨w, e, ?_⟩
  refine ⟨BlockShape.permutation_mem_singletonSplitComponent_normalizer F.Carrier w,
    P.parabolic_map_conj_of_standardizer _ m hm,
    P.splitComponent_map_conj_of_standardizer _ m hm,
    P.leviSubgroup_map_conj_of_standardizer _ m hm, ?_, ?_, hrep⟩
  · exact T.innerLeviEquiv_embedding_of_standardizer P _ m hm
  · exact T.leviRealPowerCharacter_comp_innerLeviEquiv P.shape m t

end Langlands
