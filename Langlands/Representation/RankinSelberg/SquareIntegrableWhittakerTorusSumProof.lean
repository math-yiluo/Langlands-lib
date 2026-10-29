import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumStatement
import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumCells
import Langlands.Representation.Whittaker.SmoothSimpleRootSupportProof
import Langlands.LocalField.SmoothCharacterNormProof

/-!
# Square-summability of square-integrable Whittaker functions on the torus lattice

The proof compares Whittaker functions with matrix coefficients. By the simple-root support
bound, a Whittaker function vanishes at `ϖ^μ` unless `μ` lies in a translate of the antitone
cone. On the antitone cone, a Whittaker function agrees with a smooth `K(r)`-invariant
matrix coefficient, and square-integrability modulo the centre makes these values
square-summable against the inverse modulus.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

namespace SquareIntegrableWhittakerTorusSum

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {m : ℕ}

/-- The upper-Borel modulus `∏_{i<j} |ϖ^(e_i) / ϖ^(e_j)|` of the torus element `ϖ^e`. -/
def torusModulus (ϖ : F.Carrierˣ) (e : Fin (m + 1) → ℤ) : ℝ :=
  ∏ i : Fin (m + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (m + 1) => i < j),
    T.normalizedAbs ((ϖ ^ e i / ϖ ^ e j : F.Carrierˣ) : F.Carrier)

theorem normalizedAbs_zpow (a : F.Carrierˣ) (d : ℤ) :
    T.normalizedAbs ((a ^ d : F.Carrierˣ) : F.Carrier) = T.normalizedAbs (a : F.Carrier) ^ d := by
  rw [← T.normalizedAbsUnits_coe, ← T.normalizedAbsUnits_coe, map_zpow,
    Units.val_zpow_eq_zpow_val, NNReal.coe_zpow]

/-- The modulus is multiplicative in the exponent. -/
theorem torusModulus_add (ϖ : F.Carrierˣ) (e e' : Fin (m + 1) → ℤ) :
    torusModulus T ϖ (e + e') = torusModulus T ϖ e * torusModulus T ϖ e' := by
  unfold torusModulus
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← T.normalizedAbs_mul, ← Units.val_mul, Pi.add_apply, Pi.add_apply, zpow_add, zpow_add,
    mul_div_mul_comm]

theorem torusModulus_pos (ϖ : F.Carrierˣ) (e : Fin (m + 1) → ℤ) : 0 < torusModulus T ϖ e :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => T.normalizedAbs_pos (Units.ne_zero _)

end SquareIntegrableWhittakerTorusSum

open SquareIntegrableWhittakerTorusSum

/-- **Square-summability of square-integrable Whittaker functions on the torus lattice.** -/
theorem squareIntegrableWhittakerTorusSum :
    SquareIntegrableWhittakerTorusSumStatement.{uF, uV} := by
  intro p _ F T m
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ π _hirr hsq ℓ f ϖ hϖ
  have hπ : IsSmooth π := hsq.isAdmissible.1
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
  show Summable fun lam : Fin m → ℤ =>
    (torusModulus T ϖ (Fin.snoc lam 0))⁻¹ *
      ‖ℓ.val (π (Iwasawa.torus ϖ (Fin.snoc lam 0)) v)‖ ^ 2
  -- The simple-root support bound.
  obtain ⟨R, -, hR⟩ :=
    Whittaker.smoothSimpleRootSupport.{uF, uV} F T m ψ V π hπ ℓ (modelMap π ℓ v)
  have hϖ1 : T.normalizedAbs (ϖ : F.Carrier) < 1 := by
    refine lt_of_le_of_ne ((T.normalizedAbs_le_one_iff_mem_integers _).mpr ?_) ?_
    · exact (Valuation.mem_integer_iff _ _).mpr hϖ.1.le
    · intro h
      exact hϖ.1.ne ((T.normalizedAbs_eq_one_iff_valuation_eq_one _).mp h)
  have hϖ0 : 0 < T.normalizedAbs (ϖ : F.Carrier) := T.normalizedAbs_pos ϖ.ne_zero
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R ((one_lt_inv₀ hϖ0).mpr hϖ1)
  have hsupp : ∀ e : Fin (m + 1) → ℤ, ℓ.val (π (Iwasawa.torus ϖ e) v) ≠ 0 →
      ∀ i : Fin m, -(n : ℤ) < e i.castSucc - e i.succ := by
    intro e he i
    have h1 := hR (fun i => ϖ ^ e i) 1 (one_mem _) (by rw [mul_one]; exact he) i
    beta_reduce at h1
    rw [div_eq_mul_inv, ← zpow_sub, normalizedAbs_zpow] at h1
    by_contra hle
    rw [not_lt] at hle
    have h2 : T.normalizedAbs (ϖ : F.Carrier) ^ (-(n : ℤ)) ≤
        T.normalizedAbs (ϖ : F.Carrier) ^ (e i.castSucc - e i.succ) :=
      zpow_le_zpow_right_of_le_one₀ hϖ0 hϖ1.le hle
    rw [zpow_neg, zpow_natCast, ← inv_pow] at h2
    exact absurd (hn.trans_le (h2.trans h1)) (lt_irrefl _)
  -- The shift into the antitone cone.
  let σ : Fin (m + 1) → ℤ := fun i => (n : ℤ) * ((m : ℤ) - ((i : ℕ) : ℤ))
  let σ' : Fin m → ℤ := fun i => σ i.castSucc
  have hσlast : σ (Fin.last m) = 0 := by
    simp [σ]
  have hσsnoc : ∀ lam : Fin m → ℤ,
      (Fin.snoc (lam + σ') 0 : Fin (m + 1) → ℤ) = Fin.snoc lam 0 + σ := by
    intro lam
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp [hσlast]
    · simp [σ']
  have hσstep : ∀ i : Fin m, σ i.castSucc - σ i.succ = n := by
    intro i
    simp only [σ, Fin.val_castSucc, Fin.val_succ]
    push_cast
    ring
  -- A smooth matrix coefficient agreeing with the Whittaker function on the cone.
  let v' := π (Iwasawa.torus ϖ (-σ)) v
  have hW : ∀ e, ℓ.val (π (Iwasawa.torus ϖ e) v) =
      ℓ.val (π (Iwasawa.torus ϖ (e + σ)) v') := by
    intro e
    change _ = ℓ.val (π (Iwasawa.torus ϖ (e + σ)) (π (Iwasawa.torus ϖ (-σ)) v))
    rw [← Module.End.mul_apply, ← map_mul, ← torus_add, add_neg_cancel_right]
  obtain ⟨r, hr, hv'K, L, hLs, hLK, hLeq⟩ :=
    exists_smooth_eq_on_antitone F T m ψ π hπ ℓ v' ϖ hϖ.1.le
  -- Square-integrability modulo the centre.
  let := T.centralQuotientMeasurableSpace (m + 1)
  have := T.centralQuotientBorelSpace (m + 1)
  have := T.generalLinearTopologicalGroup (m + 1)
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_centralQuotient (m + 1)
  obtain ⟨-, c, hc⟩ := hsq μ
  have hsumA : Summable fun lam : {lam : Fin m → ℤ //
      Antitone (Fin.snoc lam 0 : Fin (m + 1) → ℤ)} =>
      (torusModulus T ϖ (Fin.snoc lam.1 0))⁻¹ *
        ‖L (π (Iwasawa.torus ϖ (Fin.snoc lam.1 0)) v')‖ ^ 2 :=
    summable_antitone F T m r hr ϖ hϖ π c L v' hLK hv'K μ (hc ⟨L, hLs⟩ v')
  -- Transport along the injective shift `lam ↦ lam - σ'`.
  let j : {lam : Fin m → ℤ // Antitone (Fin.snoc lam 0 : Fin (m + 1) → ℤ)} →
      Fin m → ℤ := fun lam => lam.1 - σ'
  have hj : Function.Injective j := by
    intro a b h
    exact Subtype.ext (sub_left_injective h)
  refine (hj.summable_iff (f := fun lam : Fin m → ℤ =>
    (torusModulus T ϖ (Fin.snoc lam 0))⁻¹ *
      ‖ℓ.val (π (Iwasawa.torus ϖ (Fin.snoc lam 0)) v)‖ ^ 2) ?_).mp ?_
  · intro lam hlam
    have hzero : ℓ.val (π (Iwasawa.torus ϖ (Fin.snoc lam 0)) v) = 0 := by
      by_contra hne
      apply hlam
      have hanti : Antitone (Fin.snoc (lam + σ') 0 : Fin (m + 1) → ℤ) := by
        rw [hσsnoc, Fin.antitone_iff_succ_le]
        intro i
        have h1 := hsupp _ hne i
        have h2 := hσstep i
        simp only [Pi.add_apply]
        omega
      exact ⟨⟨lam + σ', hanti⟩, add_sub_cancel_right lam σ'⟩
    simp only [hzero, norm_zero]
    ring
  · refine (hsumA.mul_left (torusModulus T ϖ σ)).congr fun lam => ?_
    have he : (Fin.snoc (j lam) 0 : Fin (m + 1) → ℤ) + σ = Fin.snoc lam.1 0 := by
      rw [← hσsnoc, sub_add_cancel]
    have hσ0 := (torusModulus_pos T ϖ σ).ne'
    change _ = (torusModulus T ϖ (Fin.snoc (j lam) 0))⁻¹ *
      ‖ℓ.val (π (Iwasawa.torus ϖ (Fin.snoc (j lam) 0)) v)‖ ^ 2
    have hmod : torusModulus T ϖ (Fin.snoc lam.1 0) =
        torusModulus T ϖ (Fin.snoc (j lam) 0) * torusModulus T ϖ σ := by
      rw [← he, torusModulus_add]
    rw [hW, he, ← hLeq _ lam.2, hmod, mul_inv,
      mul_comm (torusModulus T ϖ (Fin.snoc (j lam) 0))⁻¹ (torusModulus T ϖ σ)⁻¹, mul_assoc,
      ← mul_assoc (torusModulus T ϖ σ), mul_inv_cancel₀ hσ0, one_mul]

end Langlands.RankinSelberg
