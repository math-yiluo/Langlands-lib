import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Langlands.HarmonicAnalysis.PrincipalUnitPowerCofinalityProof
import Langlands.LocalFactor.BrauerKernel.PlaceRamification

/-! # Ramification of the local twists under the idele-class norm -/

noncomputable section

set_option autoImplicit false

universe u uF uE

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.CompletionPadic Langlands.Global.AdelicFunctoriality
open Langlands.LocalFactor.NonabelianBrauer
open scoped NumberField WithZero FiniteExtension

private theorem canonicalCompletionDiscreteValuation {K : Type u} [Field K] [NumberField K]
    (p : FinitePlace K) : (padicField p).canonicalTopologicalData.discreteValuation = Valued.v :=
  canonicalDiscreteValuation_padicFieldAt (p := residuePrime p) p rfl

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

private theorem mem_principalUnits_completionMap (v : FinitePlace F) (w : FinitePlacesAbove E v)
    (n : ℕ) (a : (FiniteCompletion F v)ˣ)
    (ha : a ∈ (padicField v).canonicalTopologicalData.principalUnits n) :
    Units.map (FiniteExtension.completionMap v w.1).toMonoidHom a ∈
      (padicField w.1).canonicalTopologicalData.principalUnits n := by
  rw [PadicField.TopologicalData.mem_principalUnits, canonicalCompletionDiscreteValuation v] at ha
  rw [PadicField.TopologicalData.mem_principalUnits, canonicalCompletionDiscreteValuation w.1]
  change Valued.v (FiniteExtension.completionMap v w.1 (a : FiniteCompletion F v)) = 1 ∧
    Valued.v (FiniteExtension.completionMap v w.1 (a : FiniteCompletion F v) - 1) ≤ _
  refine ⟨?_, ?_⟩
  · rw [FiniteExtension.valuation_completionMap, ha.1, one_pow]
  · rw [← map_one (FiniteExtension.completionMap v w.1), ← map_sub,
      FiniteExtension.valuation_completionMap]
    refine (pow_le_pow_left' ha.2 _).trans ?_
    rw [← WithZero.exp_nsmul, nsmul_eq_mul, WithZero.exp_le_exp, mul_neg, neg_le_neg_iff]
    have he : 1 ≤ (w.1.asIdeal.ramificationIdx (𝓞 F) : ℤ) := by
      exact_mod_cast (w.1.asIdeal.ramificationIdx_pos (𝓞 F))
    exact le_mul_of_one_le_left (Int.natCast_nonneg n) he

/-- The local norm of a sufficiently deep upper principal-unit subgroup
contains a downstairs principal-unit subgroup. The depth works before choosing a character. -/
theorem exists_principalUnits_subset_range_localUnitNorm (v : FinitePlace F)
    (w : FinitePlacesAbove E v) (n : ℕ) :
    ∃ b : ℕ, ∀ a : (FiniteCompletion F v)ˣ,
      a ∈ (padicField v).canonicalTopologicalData.principalUnits b →
      ∃ x : (FiniteCompletion E w.1)ˣ,
        x ∈ (padicField w.1).canonicalTopologicalData.principalUnits n ∧
          FiniteExtension.localUnitNorm v w.1 x = a := by
  let d := Module.finrank (FiniteCompletion F v) (FiniteCompletion E w.1)
  obtain ⟨b, hb⟩ := (padicField v).canonicalTopologicalData.exists_principalUnits_subset_pow
    n d Module.finrank_pos
  refine ⟨b, fun a ha => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hb a ha
  refine ⟨Units.map (FiniteExtension.completionMap v w.1).toMonoidHom c,
    mem_principalUnits_completionMap v w n c hc, Units.ext ?_⟩
  rw [FiniteExtension.localUnitNorm_val]
  change FiniteExtension.localNorm v w.1
    (FiniteExtension.completionMap v w.1 (c : FiniteCompletion F v)) = _
  rw [FiniteExtension.localNorm_algebraMap, Units.val_pow_eq_pow_val]

/-- At any finite place of a number-field extension, sufficiently deep
ramification of the base character forces the norm pullback above a prescribed conductor. -/
def WeakInductionNormTwistDepthStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : FinitePlace F) (w : FinitePlacesAbove E v) (n : ℕ),
    ∃ b : ℕ, ∀ χ : HeckeCharacter F,
      NontrivialOnPrincipalUnits v (χ.finiteComponent v) b →
      n < (padicField w.1).canonicalTopologicalData.multiplicativeConductor
        (quasicharacterAt w.1 rfl (HeckeCharacter.finiteComponent
          (χ.comp (ideleClassNorm (K := F) (L := E))) w.1))

set_option maxHeartbeats 500000 in
theorem weakInductionNormTwistDepth : WeakInductionNormTwistDepthStatement.{uF, uE} := by
  intro F E _ _ _ _ _ v w n
  obtain ⟨b, hb⟩ := exists_principalUnits_subset_range_localUnitNorm v w n
  refine ⟨b, fun χ hχ => ?_⟩
  have hχb := lt_multiplicativeConductor_of_nontrivialOnPrincipalUnits (p := residuePrime v)
    v (χ.finiteComponent v) b hχ rfl
  obtain ⟨a, ha, hχa⟩ := (padicField v).canonicalTopologicalData.exists_nontrivial_below_multiplicativeConductor
    (quasicharacterAt v rfl (χ.finiteComponent v)) b hχb
  obtain ⟨x, hx, hnorm⟩ := hb a ha
  by_contra h
  have htriv := ((padicField w.1).canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le
    _ n).mpr (le_of_not_gt h) x hx
  change χ (ideleClassNorm (K := F)
    (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 E) E w.1 x)) = 1 at htriv
  rw [ideleClassNorm_ofAdicCompletion v w x, hnorm] at htriv
  exact hχa htriv

end Langlands.Automorphic.Unramified
