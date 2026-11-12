import Langlands.AlgebraicGeometry.PointTopology.LocalFieldUltrapower
import Langlands.AlgebraicGeometry.PointTopology.SimpleRootContinuityProof
import Mathlib.RingTheory.Henselian

/-! # The convergent germs of a complete locally compact field form a henselian ring

For a nondiscrete locally compact complete normed field `K` and an ultrafilter `𝒰`, the
valuation subring of convergent germs in the ultrapower is a henselian local ring. Its
maximal ideal consists of the germs converging to zero, and simple roots lift by continuity
of simple roots of monic polynomials over `K`.
-/

noncomputable section

universe u

open Filter Topology Polynomial

namespace Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [LocallyCompactSpace K]
  {I : Type u} {𝒰 : Ultrafilter I} {hnd : ¬ DiscreteTopology K}

/-- A convergent germ with nonzero limit is a unit of the convergent germs. -/
theorem isUnit_of_standardPart_ne_zero (a : convergentGerms K 𝒰 hnd)
    (ha : standardPart K 𝒰 hnd a ≠ 0) : IsUnit a := by
  obtain ⟨g, hg⟩ := ultrapowerMap_surjective (K := K) (𝒰 := 𝒰) (a : UltrapowerField K 𝒰)
  have hlim : Tendsto g 𝒰 (𝓝 (standardPart K 𝒰 hnd a)) :=
    tendsto_standardPart K 𝒰 hnd a hg.symm
  have hne : ∀ᶠ i in (𝒰 : Filter I), g i ≠ 0 :=
    hlim.eventually_ne ha
  have hinv : Tendsto (fun i => (g i)⁻¹) 𝒰 (𝓝 (standardPart K 𝒰 hnd a)⁻¹) :=
    (tendsto_inv₀ ha).comp hlim
  let b : convergentGerms K 𝒰 hnd :=
    ⟨ultrapowerMap K 𝒰 (fun i => (g i)⁻¹),
      (mem_convergentGerms_iff K 𝒰 hnd).2 ⟨_, hinv⟩⟩
  refine IsUnit.of_mul_eq_one b (Subtype.ext ?_)
  change (a : UltrapowerField K 𝒰) * ultrapowerMap K 𝒰 (fun i => (g i)⁻¹) = 1
  rw [← hg, ← map_mul, ← map_one (ultrapowerMap K 𝒰), ultrapowerMap_eq_iff]
  filter_upwards [hne] with i hi
  simp [hi]

/-- The maximal ideal of the convergent germs is the kernel of the standard part map. -/
theorem mem_maximalIdeal_convergentGerms_iff (a : convergentGerms K 𝒰 hnd) :
    a ∈ IsLocalRing.maximalIdeal (convergentGerms K 𝒰 hnd) ↔ standardPart K 𝒰 hnd a = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h
    by_contra hne
    exact h (isUnit_of_standardPart_ne_zero a hne)
  · intro h hu
    have := hu.map (standardPart K 𝒰 hnd)
    rw [h] at this
    exact not_isUnit_zero this

omit [LocallyCompactSpace K] in
/-- Evaluating a polynomial with germ coefficients at a germ is the germ of the pointwise
evaluations. -/
theorem eval_ultrapowerMap {n : ℕ} (g : Fin n → I → K) (a : I → K) :
    ((X ^ n + ∑ k : Fin n, C (ultrapowerMap K 𝒰 (g k)) * X ^ k.val :
        Polynomial (UltrapowerField K 𝒰))).eval (ultrapowerMap K 𝒰 a) =
      ultrapowerMap K 𝒰 (fun i =>
        (X ^ n + ∑ k : Fin n, C (g k i) * X ^ k.val : Polynomial K).eval (a i)) := by
  have hfun : (fun i =>
      (X ^ n + ∑ k : Fin n, C (g k i) * X ^ k.val : Polynomial K).eval (a i)) =
      a ^ n + ∑ k : Fin n, g k * a ^ k.val := by
    funext i
    simp [eval_finsetSum, Finset.sum_apply]
  rw [hfun]
  simp [eval_finsetSum, map_add, map_pow, map_sum, map_mul]

variable [CompleteSpace K]

/-- **The convergent germs form a henselian local ring.** -/
theorem convergentGerms_henselian : HenselianLocalRing (convergentGerms K 𝒰 hnd) where
  is_henselian := by
    classical
    intro f hf a₀ hfa₀ hda₀
    let ρ := standardPart K 𝒰 hnd
    obtain ⟨n, hn⟩ : ∃ n, f.natDegree = n := ⟨_, rfl⟩
    -- the reduced polynomial has the simple root `ρ a₀`
    have hred : ∀ (p : Polynomial (convergentGerms K 𝒰 hnd)) (x : convergentGerms K 𝒰 hnd),
        ρ (p.eval x) = (p.map ρ.toRingHom).eval (ρ x) := by
      intro p x
      rw [Polynomial.eval_map]
      exact (Polynomial.eval₂_at_apply ρ.toRingHom x).symm
    have hroot : (f.map ρ.toRingHom).eval (ρ a₀) = 0 := by
      rw [← hred]
      exact (mem_maximalIdeal_convergentGerms_iff _).1 hfa₀
    have hsimple : (f.map ρ.toRingHom).derivative.eval (ρ a₀) ≠ 0 := by
      rw [Polynomial.derivative_map, ← hred]
      exact (hda₀.map ρ).ne_zero
    -- the degree is positive
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exfalso
        have hf1 : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf (hn.trans h)
        rw [hf1, Polynomial.map_one, Polynomial.eval_one] at hroot
        exact one_ne_zero hroot
      · exact h
    -- coefficients as germs of families
    have hc : ∀ k : Fin n, ∃ g : I → K, ultrapowerMap K 𝒰 g = (f.coeff k : UltrapowerField K 𝒰) :=
      fun k => ultrapowerMap_surjective _
    choose g hg using hc
    let c : Fin n → K := fun k => ρ (f.coeff k)
    have hgc : ∀ k, Tendsto (g k) 𝒰 (𝓝 (c k)) :=
      fun k => tendsto_standardPart K 𝒰 hnd (f.coeff k) (hg k).symm
    have hgC : Tendsto (fun i k => g k i) 𝒰 (𝓝 c) := tendsto_pi_nhds.2 hgc
    -- the reduced polynomial in monic coordinate form
    have hfmap : f.map ρ.toRingHom =
        X ^ n + ∑ k : Fin n, Polynomial.C (c k) * X ^ k.val := by
      conv_lhs => rw [hf.as_sum]
      rw [hn, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
      congr 1
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [c]
    obtain ⟨ψ, hψc, hψcont, hψev, -⟩ :=
      monicSimpleRootContinuity K n hn0 c (ρ a₀) (by beta_reduce; rw [← hfmap]; exact hroot)
        (by beta_reduce; rw [← hfmap]; exact hsimple)
    -- the lifted root
    let a : I → K := fun i => ψ (fun k => g k i)
    have ha : Tendsto a 𝒰 (𝓝 (ρ a₀)) := by
      rw [← hψc]
      exact hψcont.tendsto.comp hgC
    have hev : ∀ᶠ i in (𝒰 : Filter I),
        (X ^ n + ∑ k : Fin n, Polynomial.C (g k i) * X ^ k.val : Polynomial K).eval (a i) = 0 :=
      (hgC.eventually hψev).mono fun i hi => hi.1
    let α : convergentGerms K 𝒰 hnd :=
      ⟨ultrapowerMap K 𝒰 a, (mem_convergentGerms_iff K 𝒰 hnd).2 ⟨_, ha⟩⟩
    have hρα : ρ α = ρ a₀ := standardPart_eq_of_tendsto α rfl ha
    refine ⟨α, ?_, ?_⟩
    · -- `f α = 0`, computed in the ultrapower
      show Polynomial.eval α f = 0
      apply Subtype.ext
      have hsub : ((Polynomial.eval α f : convergentGerms K 𝒰 hnd) : UltrapowerField K 𝒰) =
          (f.map (convergentGerms K 𝒰 hnd).subtype).eval (α : UltrapowerField K 𝒰) := by
        rw [Polynomial.eval_map]
        exact (Polynomial.eval₂_at_apply (convergentGerms K 𝒰 hnd).subtype α).symm
      rw [hsub]
      have hfL : f.map (convergentGerms K 𝒰 hnd).subtype =
          X ^ n + ∑ k : Fin n, Polynomial.C (ultrapowerMap K 𝒰 (g k)) * X ^ k.val := by
        conv_lhs => rw [hf.as_sum]
        rw [hn, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
        congr 1
        rw [Finset.sum_range]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [hg]
      rw [hfL]
      change Polynomial.eval (ultrapowerMap K 𝒰 a) _ = 0
      rw [eval_ultrapowerMap, ← map_zero (ultrapowerMap K 𝒰), ultrapowerMap_eq_iff]
      exact hev
    · rw [mem_maximalIdeal_convergentGerms_iff, map_sub, hρα, sub_self]

end Langlands.AlgebraicGeometry.PointTopology
