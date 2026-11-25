import Langlands.Analysis.ContinuousCharacterReal
import Langlands.Automorphic.HeckeTwist.FiniteSlice
import Langlands.Automorphic.HeckeTwist.FiniteLocalTransport
import Langlands.Global.Factors.CuspidalPairCompletedEquationReduction
import Langlands.Global.Factors.HeckeEulerProduct
import Langlands.Global.Factors.RelativeWeilLocalEulerBridge
import Langlands.Global.PositiveRealTorusLog
import Langlands.Global.RankinSelberg.SelfPairContragredient
import Langlands.Global.Factors.CuspidalSplitCentreUnitaryProof
import Langlands.Global.HeckeNormPower

/-!
# Twisting an arbitrary cuspidal realization by a complex power of the norm

Every actual cuspidal realization `T` of `GL_(r+1)` over a number field becomes trivial on the
split centre `A_(GL_(r+1))` after a twist by `‖·‖^(-λ) ∘ det` for some complex `λ`
(`HeckeCharacter.normPower`). By the proved split-centre unitarity, the twist then has a unitary
central character. This is the decomposition `π = π₀ ⊗ |det|^λ` with `π₀` unitary used by
Jacquet–Shalika II, (4.2).

The values of `‖·‖^s` at the chosen uniformizers are `q_v^(-s)`
(`finiteUniformizerValue_normPower`).
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Global

open NumberField PositiveRealTorus
open scoped NNReal
open Automorphic (CuspidalOperatorRealization OperatorRealization centralIdeleCharacter)
open Automorphic.ContinuousRationalFunctions (evaluate)
open CuspidalPairPoles
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

namespace NormPowerTwist

variable {F : Type u} [Field F] [NumberField F]

set_option maxHeartbeats 1000000 in
/-- Every idele of `A_(G_m)` is a positive real idele `PositiveRealIdeles.full F t`. -/
private theorem eq_full_of_isPositiveArchimedeanScalar {a : IdeleGroup (𝓞 F) F}
    (ha : IsPositiveArchimedeanScalar a) : ∃ t : ℝ≥0ˣ, a = PositiveRealIdeles.full F t := by
  obtain ⟨hfin, t, ht, hinf⟩ := ha
  let T : ℝ≥0ˣ := Units.mk0 ⟨t, ht.le⟩ (by
    intro h
    have := congrArg NNReal.toReal h
    simp only [NNReal.coe_zero] at this
    exact ht.ne' this)
  refine ⟨T, ?_⟩
  apply Units.ext
  apply Prod.ext
  · funext v
    apply (InfinitePlace.Completion.extensionEmbedding v).injective
    rw [hinf v]
    exact (PositiveRealIdeles.extensionEmbedding_full F v T).symm
  · rw [hfin]
    rfl

set_option maxHeartbeats 2000000 in
/-- A realization whose central character is trivial on the positive real ideles is trivial on
the split centre. -/
private theorem isTrivialOnSplitCentre_of_hasCentralCharacter {r : ℕ}
    [CompactSpace (AdeleQuotient F)] (T : CuspidalOperatorRealization F r)
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (hχ : T.HasCentralCharacter χ)
    (h1 : ∀ t : ℝ≥0ˣ, centralIdeleCharacter F χ (PositiveRealIdeles.full F t) = 1) :
    IsTrivialOnSplitCentre T := by
  intro a ha f x
  obtain ⟨t, ht⟩ := eq_full_of_isPositiveArchimedeanScalar ha
  have h := T.realization.centralCharacter_evaluate χ hχ f (PositiveRealIdeles.full F t) x
  rw [h1 t, Units.val_one, one_mul] at h
  rw [ht]
  exact h

/-- A character of the idele classes is `u ↦ exp (μ u)` on the positive real ideles
`PositiveRealIdeles.full F (e ^ u)`, for one complex `μ`. -/
theorem exists_eq_exp_on_full (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) :
    ∃ μ : ℂ, ∀ u : ℝ, ((centralIdeleCharacter F χ (PositiveRealIdeles.full F
      (PositiveRealTorus.expUnit u)) :
      ℂˣ) : ℂ) = Complex.exp (μ * u) := by
  let φ : ℝ → ℂ := fun u =>
    ((centralIdeleCharacter F χ (PositiveRealIdeles.full F (PositiveRealTorus.expUnit u)) :
      ℂˣ) : ℂ)
  have hc : Continuous φ :=
    Units.continuous_val.comp ((centralIdeleCharacter F χ).continuous.comp
      ((PositiveRealIdeles.full F).continuous.comp PositiveRealTorus.continuous_expUnit))
  have h0 : φ 0 = 1 := by
    have h := expUnit_log (1 : ℝ≥0ˣ)
    have hzero : PositiveRealTorus.expUnit 0 = (1 : ℝ≥0ˣ) := by simpa using h
    simp [φ, hzero]
  have hadd : ∀ u v, φ (u + v) = φ u * φ v := by
    intro u v
    have hExp : PositiveRealTorus.expUnit (u + v) =
        PositiveRealTorus.expUnit u * PositiveRealTorus.expUnit v := by
      apply Units.ext
      apply NNReal.eq
      simp [Real.exp_add]
    simp only [φ, hExp, map_mul, Units.val_mul]
  exact ContinuousCharacterReal.exists_eq_exp hc h0 hadd

/-- The norm power `‖·‖ ^ s` on `PositiveRealIdeles.full F (e ^ u)` is `exp (s [F : ℚ] u)`. -/
theorem normPower_full_expUnit (s : ℂ) (u : ℝ) :
    ((centralIdeleCharacter F (HeckeCharacter.normPower F s)
        (PositiveRealIdeles.full F (PositiveRealTorus.expUnit u)) : ℂˣ) : ℂ) =
      Complex.exp (s * (((Module.finrank ℚ F : ℝ) * u : ℝ) : ℂ)) := by
  change ((HeckeCharacter.normPower F s
      (ideleClassMap F (PositiveRealIdeles.full F (PositiveRealTorus.expUnit u))) : ℂˣ) : ℂ) = _
  rw [HeckeCharacter.normPower_apply, IdeleAbsoluteValue.ideleClass_class,
    PositiveRealIdeles.absoluteValue_full, Units.val_pow_eq_pow_val, NNReal.coe_pow,
    PositiveRealTorus.coe_expUnit, Real.log_pow, Real.log_exp]

/-- **Twisting to the split centre.** Every actual cuspidal realization becomes trivial on the
split centre after a twist by `‖·‖^(-λ) ∘ det` for some complex `λ`. -/
theorem exists_normPower_twist_isTrivialOnSplitCentre {r : ℕ} [CompactSpace (AdeleQuotient F)]
    (T : CuspidalOperatorRealization F r) :
    ∃ l : ℂ, IsTrivialOnSplitCentre (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-l))) := by
  obtain ⟨ω, hω, -⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
  obtain ⟨μ, hμ⟩ := exists_eq_exp_on_full ω
  have hd : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos
  set l : ℂ := μ / ((Module.finrank ℚ F : ℂ) * ((r : ℂ) + 1)) with hl
  refine ⟨l, ?_⟩
  have hc : (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-l))).HasCentralCharacter
      (HeckeCharacter.normPower F (-l) ^ (r + 1) * ω) := by
    change (T.realization.heckeDeterminantTwist _).toFiniteRealization.HasCentralCharacter _
    rw [OperatorRealization.toFiniteRealization_heckeDeterminantTwist]
    exact T.realization.toFiniteRealization.heckeDeterminantTwist_hasCentralCharacter _ ω hω
  refine isTrivialOnSplitCentre_of_hasCentralCharacter _ _ hc (fun t => ?_)
  rw [← expUnit_log t]
  set u := Real.log ((t : ℝ≥0) : ℝ)
  apply Units.ext
  have hmul : ((centralIdeleCharacter F (HeckeCharacter.normPower F (-l) ^ (r + 1) * ω)
      (PositiveRealIdeles.full F (PositiveRealTorus.expUnit u)) : ℂˣ) : ℂ) =
      ((centralIdeleCharacter F (HeckeCharacter.normPower F (-l))
        (PositiveRealIdeles.full F (PositiveRealTorus.expUnit u)) : ℂˣ) : ℂ) ^ (r + 1) *
      ((centralIdeleCharacter F ω (PositiveRealIdeles.full F (PositiveRealTorus.expUnit u)) :
        ℂˣ) : ℂ) := by
    change (((HeckeCharacter.normPower F (-l) ^ (r + 1) * ω) _ : ℂˣ) : ℂ) = _
    rw [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.pow_apply, Units.val_mul,
      Units.val_pow_eq_pow_val]
    rfl
  rw [hmul, normPower_full_expUnit, hμ u, ← Complex.exp_nat_mul, ← Complex.exp_add,
    Units.val_one]
  rw [← Complex.exp_zero]
  congr 1
  rw [hl]
  have hdC : (Module.finrank ℚ F : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hrC : ((r : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  push_cast
  field_simp
  ring

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Triviality on the split centre passes to the complex conjugate realization. -/
theorem isTrivialOnSplitCentre_conjugate {r : ℕ} [CompactSpace (AdeleQuotient F)]
    {T : CuspidalOperatorRealization F r} (hT : IsTrivialOnSplitCentre T) :
    IsTrivialOnSplitCentre T.conjugate := by
  intro a ha f x
  obtain ⟨g, rfl⟩ := T.realization.conjugateEquiv.surjective f
  change evaluate F (r + 1)
      (T.realization.conjugate.toContinuous (T.realization.conjugateEquiv g))
      (AdelicGL.scalar F (r + 1) a * x) =
    evaluate F (r + 1) (T.realization.conjugate.toContinuous (T.realization.conjugateEquiv g)) x
  rw [OperatorRealization.evaluate_conjugateEquiv, OperatorRealization.evaluate_conjugateEquiv,
    hT a ha g x]

/-- The twist of the main theorem has a unitary central character and is trivial on the split
centre, and so is its conjugate, which realizes its contragredient. -/
theorem exists_normPower_twist {r : ℕ} [CompactSpace (AdeleQuotient F)]
    (T : CuspidalOperatorRealization F r) :
    ∃ l : ℂ,
      HasUnitaryCentralCharacter (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-l))) ∧
      IsTrivialOnSplitCentre (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-l))) ∧
      IsTrivialOnSplitCentre (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-l))).conjugate ∧
      HasUnitaryCentralCharacter
        (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-l))).conjugate ∧
      (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-l))).conjugate.realization.IsContragredientOf
        (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-l))).realization := by
  obtain ⟨l, hl⟩ := exists_normPower_twist_isTrivialOnSplitCentre T
  have hu := cuspidalSplitCentreUnitaryCentralCharacter F r _ hl
  have hc := isTrivialOnSplitCentre_conjugate hl
  exact ⟨l, hu, hl, hc, cuspidalSplitCentreUnitaryCentralCharacter F r _ hc,
    RankinSelbergGlobal.SelfPair.conjugate_isContragredientOf _ hu⟩

/-- The value of `‖·‖ ^ s` at the chosen uniformizer of `F_v` is `q_v ^ (-s)`. -/
theorem finiteUniformizerValue_normPower (s : ℂ) (v : FinitePlace F) :
    ((HeckeCharacter.normPower F s).finiteUniformizerValue v : ℂ) =
      (CuspidalPairFunctionalEquation.residueCardinality v : ℂ) ^ (-s) := by
  have hN := HeckeEulerProduct.norm_uniformizerUnit v
  rw [CompletionPadic.topologicalData_eq_canonicalTopologicalData] at hN
  change ((HeckeCharacter.normPower F s).finiteComponent v
    (CompletionPadic.padicField v).canonicalTopologicalData.uniformizerUnit : ℂ) = _
  rw [HeckeCharacter.normPower_finiteComponent]
  rw [CuspidalPairEulerConvergence.residueCardinality_eq_absNorm]
  erw [hN]
  rw [Real.log_inv]
  have hq0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    have := CuspidalPairEulerConvergence.two_le_residueCardinality v
    rw [CuspidalPairEulerConvergence.residueCardinality_eq_absNorm] at this
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg _)]
  push_cast
  ring_nf
end NormPowerTwist

end Langlands.Global
