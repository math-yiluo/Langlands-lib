import Langlands.Global.CompletionPadicTower
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.Global.AdelicFunctoriality.CompletedRamification
import Langlands.Global.Factors.RelativeWeilLocalEulerBridge
import Langlands.Global.Arithmetic.CharacterPrescriptionStatement

/-! # Ramification and conductors of completions in their canonical packages -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Global Langlands.Global.CompletionPadic Langlands.Global.AdelicFunctoriality
open scoped NumberField WithZero

section Valuation

variable {K : Type u} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

/-- The normalized discrete valuation of the canonical realization of a completion, over any
prime equal to its residue prime, is the valuation of the completion. -/
theorem canonicalDiscreteValuation_padicFieldAt {p : ℕ} [Fact p.Prime] (h : residuePrime w = p) :
    (padicFieldAt w h).canonicalTopologicalData.discreteValuation =
      (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰) := by
  subst h
  refine discreteValuation_eq_of_vle _ _ (fun x y => ?_) (w.valuedAdicCompletion_surjective K)
  rw [PadicField.canonicalTopologicalData_vle, ← PadicField.canonicalValuation_coe,
    ← PadicField.canonicalValuation_coe, NNReal.coe_le_coe]
  exact (valued_isEquiv w x y).symm

end Valuation

section Ramification

variable {k 𝕃 : Type u} [Field k] [Field 𝕃] [NumberField k] [NumberField 𝕃] [Algebra k 𝕃]
  (z : HeightOneSpectrum (𝓞 k)) (u : HeightOneSpectrum (𝓞 𝕃)) [u.asIdeal.LiesOver z.asIdeal]

/-- **Unramified completions.** If `u` has ramification index one over `z`, the canonical
packages of `𝕃_u` and `k_z` over the residue prime of `z` have the same absolute ramification
index. -/
theorem ramificationIndex_towerPadicField_eq (he : u.asIdeal.ramificationIdx (𝓞 k) = 1) :
    (towerPadicField z u).canonicalTopologicalData.ramificationIndex =
      (padicField z).canonicalTopologicalData.ramificationIndex := by
  unfold PadicField.TopologicalData.ramificationIndex PadicField.TopologicalData.ord
  have h1 := canonicalDiscreteValuation_padicFieldAt u (residuePrime_eq z u)
  have h2 : (padicField z).canonicalTopologicalData.discreteValuation =
      (Valued.v : Valuation (z.adicCompletion k) ℤᵐ⁰) :=
    canonicalDiscreteValuation_padicFieldAt (p := residuePrime z) z rfl
  rw [h1, h2]
  have hcast : ((residuePrime z : ℕ) : u.adicCompletion 𝕃) =
      FiniteExtension.completionMap z u ((residuePrime z : ℕ) : z.adicCompletion k) :=
    (map_natCast (FiniteExtension.completionMap z u) _).symm
  change (-WithZero.log (Valued.v ((residuePrime z : ℕ) : u.adicCompletion 𝕃))).toNat = _
  rw [hcast, FiniteExtension.valuation_completionMap, he, pow_one]

end Ramification

section Conductor

variable {K : Type u} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

/-- An element of the maximal ideal of the completed integers has valuation at most `exp (-1)`. -/
theorem valued_le_exp_neg_one_of_mem_maximalIdeal (x : w.adicCompletionIntegers K)
    (hx : x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers K)) :
    Valued.v (x : w.adicCompletion K) ≤ WithZero.exp (-1 : ℤ) := by
  have hle : Valued.v (x : w.adicCompletion K) ≤ 1 := x.2
  have hlt : Valued.v (x : w.adicCompletion K) < 1 := by
    refine lt_of_le_of_ne hle fun h1 => hx ?_
    have hx0 : (x : w.adicCompletion K) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : w.adicCompletion K)⁻¹ ∈ w.adicCompletionIntegers K := by
      change Valued.v ((x : w.adicCompletion K)⁻¹) ≤ 1
      rw [map_inv₀, h1, inv_one]
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : w.adicCompletionIntegers K) (Subtype.ext ?_)
    change (x : w.adicCompletion K) * (x : w.adicCompletion K)⁻¹ = 1
    exact mul_inv_cancel₀ hx0
  rcases eq_or_ne (Valued.v (x : w.adicCompletion K)) 0 with h0 | h0
  · rw [h0]
    exact zero_le
  · rw [← WithZero.exp_log h0] at hlt ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    rw [WithZero.exp_le_exp]
    omega

/-- An element of the `r`-th power of the maximal ideal of the completed integers has valuation
at most `exp (-r)`. -/
theorem valued_le_exp_neg_of_mem_maximalIdeal_pow (r : ℕ) (x : w.adicCompletionIntegers K)
    (hx : x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers K) ^ r) :
    Valued.v (x : w.adicCompletion K) ≤ WithZero.exp (-(r : ℤ)) := by
  induction r generalizing x with
  | zero =>
    simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact x.2
  | succ r ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · change Valued.v ((a : w.adicCompletion K) * (b : w.adicCompletion K)) ≤ _
      rw [map_mul]
      calc Valued.v (a : w.adicCompletion K) * Valued.v (b : w.adicCompletion K)
          ≤ WithZero.exp (-(r : ℤ)) * WithZero.exp (-1 : ℤ) :=
            mul_le_mul' (ih a ha) (valued_le_exp_neg_one_of_mem_maximalIdeal w b hb)
        _ = WithZero.exp (-((r + 1 : ℕ) : ℤ)) := by
            rw [← WithZero.exp_add]
            congr 1
            push_cast
            ring
    · change Valued.v ((a : w.adicCompletion K) + (b : w.adicCompletion K)) ≤ _
      exact (Valued.v.map_add _ _).trans (max_le ha hb)

/-- A Hecke character unramified at `w` has an unramified component in the canonical
realization of `K_w`. -/
theorem isUnramifiedQuasicharacter_quasicharacterAt (Λ : HeckeCharacter K)
    (hΛ : Λ.IsUnramifiedAt w) {p : ℕ} [Fact p.Prime] (h : residuePrime w = p) :
    (padicFieldAt w h).canonicalTopologicalData.IsUnramifiedQuasicharacter
      (quasicharacterAt w h (Λ.finiteComponent w)) := by
  intro x hx
  rw [canonicalDiscreteValuation_padicFieldAt w h] at hx
  exact hΛ x (adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hx)

/-- A character nontrivial on the principal units of level `r` has conductor exponent larger
than `r` in the canonical realization of `K_w`. -/
theorem lt_multiplicativeConductor_of_nontrivialOnPrincipalUnits
    (η : (FiniteCompletion K w)ˣ →ₜ* ℂˣ) (r : ℕ) (hη : NontrivialOnPrincipalUnits w η r)
    {p : ℕ} [Fact p.Prime] (h : residuePrime w = p) :
    r < (padicFieldAt w h).canonicalTopologicalData.multiplicativeConductor
      (quasicharacterAt w h η) := by
  by_contra hle
  push Not at hle
  have htriv := ((padicFieldAt w h).canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le
    _ r).mpr hle
  obtain ⟨a, ha1, ha2⟩ := hη
  apply ha2
  apply htriv
  rw [PadicField.TopologicalData.mem_principalUnits, canonicalDiscreteValuation_padicFieldAt w h]
  constructor
  · exact (adicCompletionIntegers.isUnit_iff_valued_eq_one (a := (a : w.adicCompletionIntegers K))).mp
      a.isUnit
  · have hv := valued_le_exp_neg_of_mem_maximalIdeal_pow w r
      ((a : w.adicCompletionIntegers K) - 1) ha1
    have hcoe : ((((a : w.adicCompletionIntegers K) - 1 : w.adicCompletionIntegers K)) :
        w.adicCompletion K) = ((a : w.adicCompletionIntegers K) : w.adicCompletion K) - 1 := by
      push_cast
      rfl
    rw [hcoe] at hv
    exact hv

end Conductor

end Langlands.LocalFactor.NonabelianBrauer
