import Langlands.LocalFactor.SpectralConductorEpsilon
import Langlands.LocalFactor.SpectralConductorRankOneBridge
import Langlands.LocalFactor.SpectralConductorDegree
import Langlands.LocalFactor.SpectralConductorChoice
import Langlands.LocalFactor.CommonClosureGenerationProof
import Langlands.LocalFactor.Ramification.InertiaPresentationStatement

/-!
# Tate's spectral conductor formula from refinement and rank-one transport

Tate (3.4.5) and Deligne (5.5.2) for a supplied local-constant system follow from
two propositions: invariance of the presentation conductor under enlarging the
presenting finite Galois subfield, and the rank-one conductor transport at the
intermediate fields of the common closure.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.SpectralConductor

open CommonClosure CommonClosureSpectral CommonClosureSpectralAnalytic ConductorExponent
open VirtualRepresentation NonabelianSystem Ramification.Padic Weil.Local

/-- The reduction of Tate's spectral conductor formula to refinement invariance
of presentation conductors and rank-one conductor transport. -/
def SpectralConductorRankOneReductionStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p),
    (∀ A : FiniteRepresentation.{0, uF, max uF uV} ℂ (localWeilGroup F),
      FiniteInertiaConductorRefinementStatement.{uF, max uF uV} F A) →
    CommonClosureRankOneConductorStatement F →
    SpectralConductorStatement.{uF, uV} F

theorem spectralConductorRankOneReduction :
    SpectralConductorRankOneReductionStatement.{uF, uV} := by
  intro p _ F href hR e ε hε ψ μ A hA P hsurj s
  have hgen : CommonClosureDegreeZeroGeneration.{uF, uV} F :=
    commonClosureDegreeZeroGeneration p F
  set x := baseClass F A hA
  obtain ⟨S₀, hS₀, hx⟩ := exists_finset_generators hgen (base F) x
  obtain ⟨M, hPM, hgood⟩ := exists_presentingField F S₀ hS₀ P.extension
  have hM : Function.Surjective (weilInertiaRestriction F M) :=
    Ramification.HerbrandBridge.weilInertiaRestriction_surjective F M
  let a : Virtual.{uF, uV} F (base F) →+ ℂ :=
    (AddMonoidHom.mulRight (logCardinality (base F))).comp (conductorFunctional.{uF, uV} F M)
  have ha (y : Virtual.{uF, uV} F (base F)) :
      a y = conductorFunctional.{uF, uV} F M y * logCardinality (base F) := rfl
  have hone : a (ExactGrothendieckGroup.characterClass
      (1 : weilSubgroup F (base F) →ₜ* ℂˣ)) = 0 := by
    rw [ha, conductorFunctional_one, zero_mul]
  have hS : (S₀ : Set (Virtual.{uF, uV} F (base F))) ⊆ formulaSubgroup hε (base F) ψ μ s a := by
    intro y hy
    obtain ⟨L, h, χ, χ', hLM, rfl, hχ, hχ'⟩ := hgood y hy
    apply induce_mem_formulaSubgroup hε (base F) ψ μ s a L h χ χ'
    rw [ha, conductorFunctional_induce_eq F M L hLM h χ χ' hχ hχ',
      lClassSum_eq_characterConductor χ hχ hR e hε.1,
      lClassSum_eq_characterConductor χ' hχ' hR e hε.1,
      ← inductionFactor_mul_logCardinality e L M hLM hε.1]
    ring
  have key := mem_formulaSubgroup_of_span hε (base F) ψ μ s a S₀ hS
    (one_mem_formulaSubgroup hε (base F) ψ μ s a hone) x hx
  have hart : conductorFunctional.{uF, uV} F M x = ((P.artinConductor hsurj : ℚ) : ℂ) := by
    rw [conductorFunctional_baseClass F M A hA P hPM hM,
      ((href _ P M hPM hsurj hM).1)]
  have hdeg : (degree F (base F) x : ℂ) = (A.rank : ℂ) := by
    simp [x, baseClass, ExactGrothendieckGroup.degree_ofRepresentation]
  have hlog : logCardinality (base F) = Complex.log (baseCardinality F : ℂ) := by
    unfold logCardinality
    rw [residueCardinality_base, Complex.ofReal_log (Nat.cast_nonneg _)]
    rfl
  have hq : (baseCardinality F : ℂ) ≠ 0 := by
    exact_mod_cast (baseCardinality_pos F).ne'
  rw [conditionalDeligneValue_zero]
  change (ε (base F) ψ μ (virtualTwist F (base F) s x) : ℂ) = _
  rw [key, ha, hart, hdeg, hlog, Complex.cpow_def_of_ne_zero hq]
  congr 2
  unfold additiveConductor
  ring

end Langlands.LocalFactor.SpectralConductor
