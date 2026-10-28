import Langlands.HarmonicAnalysis.Distribution.HomogeneousVanishingStatement
import Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityProof
import Langlands.HarmonicAnalysis.AlgebraicIntegrand

/-!
# Vanishing of homogeneous anti-invariant distributions

Positive rational comparison of compact-clopen indicator values, together with
anti-invariance, forces every indicator value to vanish. A finite-fiber
expansion then proves vanishing on all Schwartz–Bruhat functions.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

open Hecke.TestFunction

universe uG uX

private theorem eq_zero_of_characteristic_eq_zero
    {X : Type uX} [TopologicalSpace X] (D : Distribution X)
    (hD : ∀ (U : Set X) (hU : IsClopen U) (hcU : IsCompact U),
      D (characteristic hU hcU) = 0) : D = 0 := by
  classical
  ext f
  let S : Set ℂ := {c | c ∈ Set.range f ∧ c ≠ 0}
  have hS : S.Finite :=
    (finite_range_of_locallyConstant_of_hasCompactSupport
      f.locallyConstant f.hasCompactSupport).subset (fun _ hc => hc.1)
  let : Fintype S := hS.fintype
  let φ : S → SchwartzBruhat X := fun c =>
    characteristic (f.locallyConstant.isClopen_fiber c.val)
      (isCompact_fiber f c.property.2)
  have heq : f = ∑ c : S, c.val • φ c := by
    apply Hecke.TestFunction.ext
    intro x
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    by_cases hx : f x = 0
    · have hne (c : S) : (0 : ℂ) ≠ c.val := Ne.symm c.property.2
      simp [φ, characteristic_apply, hne, hx]
    · let c : S := ⟨f x, ⟨⟨x, rfl⟩, hx⟩⟩
      rw [Finset.sum_eq_single c]
      · simp [φ, c, characteristic_apply]
      · intro b _ hbc
        have hne : f x ≠ b.val := by
          intro h
          exact hbc (Subtype.ext h.symm)
        simp [φ, characteristic_apply, hne]
      · simp
  rw [heq, map_sum]
  simp only [map_smul]
  have hz (c : S) : D (φ c) = 0 := hD _ _ _
  simp [hz]

private theorem eq_zero_of_positive_indicator_proportionality
    {X : Type uX} [TopologicalSpace X] (σ : X ≃ₜ X) (D : Distribution X)
    (hpositive : ∀ (U V : Set X) (hU : IsClopen U) (hcU : IsCompact U)
      (hV : IsClopen V) (hcV : IsCompact V), U.Nonempty → V.Nonempty →
      ∃ q : ℚ, 0 < q ∧ D (characteristic hU hcU) =
        (q : ℂ) * D (characteristic hV hcV))
    (hanti : pushforward σ D = -D) : D = 0 := by
  apply eq_zero_of_characteristic_eq_zero D
  intro U hU hcU
  by_cases hne : U.Nonempty
  · let V : Set X := σ ⁻¹' U
    have hV : IsClopen V := hU.preimage σ.continuous
    have hcV : IsCompact V := σ.isCompact_preimage.mpr hcU
    have hneV : V.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨σ.symm x, by simpa [V] using hx⟩
    obtain ⟨q, hq, hcompare⟩ := hpositive V U hV hcV hU hcU hneV hne
    have hpull : pullback σ (characteristic hU hcU) = characteristic hV hcV := by
      ext x
      simp only [pullback_apply, characteristic_apply]
      rfl
    have hantiU : D (characteristic hV hcV) = -D (characteristic hU hcU) := by
      have h := congrArg (fun E : Distribution X => E (characteristic hU hcU)) hanti
      simpa only [pushforward_apply, hpull, LinearMap.neg_apply] using h
    have hqone : (q : ℂ) + 1 ≠ 0 := by
      have hqone' : q + 1 ≠ 0 := ne_of_gt (by linarith)
      exact_mod_cast hqone'
    have hmul : ((q : ℂ) + 1) * D (characteristic hU hcU) = 0 := by
      rw [add_mul, one_mul, ← hcompare, hantiU, neg_add_cancel]
    exact (mul_eq_zero.mp hmul).resolve_left hqone
  · have hzero : characteristic hU hcU = 0 := by
      ext x
      simp only [characteristic_apply]
      have hx : x ∉ U := fun hx => hne ⟨x, hx⟩
      exact Set.indicator_of_notMem hx _
    rw [hzero, map_zero]

private theorem homogeneousAntiInvariantVanishing_of_proportionality
    (hproportionality : HomogeneousIndicatorProportionalityStatement.{uG, uX}) :
    HomogeneousAntiInvariantVanishingStatement.{uG, uX} := by
  intro G _ _ _ _ _ X _ _ _ _ _ _ σ D hG hanti
  exact eq_zero_of_positive_indicator_proportionality σ D
    (hproportionality G X D hG) hanti

/-- An invariant algebraic distribution on a homogeneous space vanishes if
pushforward by any homeomorphism negates it. -/
theorem homogeneousAntiInvariantVanishing :
    HomogeneousAntiInvariantVanishingStatement.{uG, uX} :=
  homogeneousAntiInvariantVanishing_of_proportionality
    homogeneousIndicatorProportionality.{uG, uX}

end Langlands.HarmonicAnalysis.Distribution
