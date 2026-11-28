import Langlands.BaseChange.UnramifiedDeterminant
import Langlands.Representation.CuspidalSupport.LeviGapVanishing
import Langlands.Group.GL.LocalFieldTopology
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # Unimodularity of the general linear group of a non-archimedean local field -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory GeneralLinear
open scoped NNReal ENNReal

universe v w

section Algebraic

variable {E : Type v} [Field E] {n : ℕ}

/-- A homomorphism to a commutative group takes the same value on the diagonal matrices
with one entry `a` in two different slots. -/
theorem map_diagonalUnits_mulSingle_eq_of_commGroup {C : Type w} [CommGroup C]
    (ψ : GeneralLinear n E →* C) (i j : Fin n) (a : Eˣ) :
    ψ (Iwasawa.diagonalUnits (Pi.mulSingle i a)) =
      ψ (Iwasawa.diagonalUnits (Pi.mulSingle j a)) := by
  classical
  let p := Equiv.swap i j
  have hp : p i = j := Equiv.swap_apply_left _ _
  have hh : (fun k => Pi.mulSingle (M := fun _ => Eˣ) i a (p⁻¹ k)) = Pi.mulSingle j a := by
    funext k
    have he : p⁻¹ k = i ↔ k = j := by
      change p.symm k = i ↔ k = j
      rw [Equiv.symm_apply_eq, hp]
    by_cases hk : k = j
    · rw [he.mpr hk, hk, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne (mt he.mp hk), Pi.mulSingle_eq_of_ne hk]
  have h := GeneralLinear.permutation_mul_diagonalUnits n p (Pi.mulSingle i a)
  rw [hh] at h
  have h' := congrArg ψ h
  simp only [map_mul] at h'
  rw [mul_comm (ψ (permutation n E p))] at h'
  exact mul_right_cancel h'

/-- A homomorphism to a commutative group evaluates on a diagonal power matrix through the
value on one diagonal slot. -/
theorem map_torus_of_commGroup {C : Type w} [CommGroup C]
    (ψ : GeneralLinear n E →* C) (i : Fin n) (a : Eˣ) (lam : Fin n → ℤ) :
    ψ (Iwasawa.torus a lam) = ψ (Iwasawa.diagonalUnits (Pi.mulSingle i a)) ^ (∑ j, lam j) := by
  classical
  let d : Fin n → Eˣ := fun j => a ^ lam j
  let φ := ψ.comp Iwasawa.diagonalUnits
  have hsum (s : Finset (Fin n)) (z : C) : z ^ (∑ j ∈ s, lam j) = ∏ j ∈ s, z ^ lam j := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hjs ih => rw [Finset.sum_insert hjs, Finset.prod_insert hjs, zpow_add, ih]
  change φ d = _
  rw [← Finset.univ_prod_mulSingle d, map_prod, hsum]
  refine Finset.prod_congr rfl fun j _ => ?_
  change φ (Pi.mulSingle j (a ^ lam j)) = _
  rw [Pi.mulSingle_zpow, map_zpow]
  exact congrArg (fun x : C => x ^ lam j) (map_diagonalUnits_mulSingle_eq_of_commGroup ψ j i a)

/-- The scalar matrix `a` is central. -/
theorem torus_const_commute (a : Eˣ) (h : GeneralLinear n E) :
    h * Iwasawa.torus a (fun _ => 1) = Iwasawa.torus a (fun _ => 1) * h := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Iwasawa.torus_val]
  ext i j
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

end Algebraic

section Local

variable (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- Right translates of a Haar measure are the modular character multiples. -/
theorem map_mul_right_eq_modularCharacter_smul (n : ℕ)
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure] (g : GeneralLinear n E) :
    letI := LocalFieldTopology.generalLinear_locallyCompactSpace E n
    μ.map (· * g) = Measure.modularCharacterFun g • μ := by
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E n
  let := LocalFieldTopology.generalLinear_secondCountableTopology E n
  rw [Measure.modularCharacterFun_eq_haarScalarFactor μ g]
  exact Measure.isMulLeftInvariant_eq_smul _ μ

/-- The modular character of `GL_n` over a non-archimedean local field is trivial. -/
theorem modularCharacterFun_generalLinear (n : ℕ) (g : GeneralLinear n E) :
    letI := LocalFieldTopology.generalLinear_locallyCompactSpace E n
    Measure.modularCharacterFun g = 1 := by
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E n
  let := LocalFieldTopology.generalLinear_secondCountableTopology E n
  let := LocalFieldTopology.generalLinear_t2Space E n
  borelize (GeneralLinear n E)
  let μ : Measure (GeneralLinear n E) := Measure.haar
  let Δ : GeneralLinear n E →* ℝ≥0 := Measure.modularCharacter
  change Δ g = 1
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hg : g = 1 := Units.ext (Matrix.ext fun i _ => i.elim0)
    rw [hg, map_one]
  let T := LocalFieldData.ofInstances E
  let v := ValuativeRel.valuation E
  let K := Iwasawa.integralRange v n
  have hKo : IsOpen (K : Set (GeneralLinear n E)) :=
    CuspidalSupport.LeviAdmissibility.isOpen_integralRange n
  have hKc : IsCompact (K : Set (GeneralLinear n E)) :=
    CuspidalSupport.LeviAdmissibility.isCompact_integralRange n
  have hK0 : μ K ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hKt : μ K ≠ ∞ := hKc.measure_lt_top.ne
  have hfix (k : GeneralLinear n E) (hk : (μ.map (· * k)) K = μ K) : Δ k = 1 := by
    have h := congrArg (fun ν : Measure (GeneralLinear n E) => ν K)
      (map_mul_right_eq_modularCharacter_smul E n μ k)
    change (μ.map (· * k)) K = (Measure.modularCharacterFun k • μ) K at h
    rw [hk, Measure.smul_apply] at h
    change μ K = ((Measure.modularCharacterFun k : ℝ≥0) : ℝ≥0∞) * μ K at h
    have h1 : ((Measure.modularCharacterFun k : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by
      rw [one_mul]
      exact h.symm
    have h2 := (ENNReal.mul_left_inj hK0 hKt).mp h1
    exact_mod_cast h2
  have hΔK (k : GeneralLinear n E) (hk : k ∈ K) : Δ k = 1 := by
    apply hfix k
    rw [Measure.map_apply (measurable_mul_const k) hKo.measurableSet]
    have hpre : (fun x => x * k) ⁻¹' (K : Set (GeneralLinear n E)) = K := by
      ext x
      simp only [Set.mem_preimage, SetLike.mem_coe]
      exact ⟨fun hx => by simpa using K.mul_mem hx (K.inv_mem hk), fun hx => K.mul_mem hx hk⟩
    rw [hpre]
  have hcentral (z : GeneralLinear n E) (hz : ∀ h : GeneralLinear n E, h * z = z * h) :
      Δ z = 1 := by
    apply hfix z
    have hf : (fun x : GeneralLinear n E => x * z) = (fun x => z * x) := funext hz
    rw [hf, map_mul_left_eq_self μ z]
  have hπ : Iwasawa.IsUniformizingElement v T.uniformizerUnit :=
    AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof.isUniformizingElement T
  let i0 : Fin n := ⟨0, hn⟩
  let Δu : GeneralLinear n E →* ℝ≥0ˣ := Δ.toHomUnits
  have hd : Δ (Iwasawa.diagonalUnits (Pi.mulSingle i0 T.uniformizerUnit)) = 1 := by
    have hs := map_torus_of_commGroup Δu i0 T.uniformizerUnit (fun _ => 1)
    rw [hcentral _ (torus_const_commute T.uniformizerUnit) |> fun h => (show Δu _ = 1 from
      Units.ext h)] at hs
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      zpow_natCast] at hs
    have hs' := congrArg (fun u : ℝ≥0ˣ => (u : ℝ≥0)) hs
    simp only [Units.val_one, Units.val_pow_eq_pow_val] at hs'
    exact (pow_eq_one_iff_of_nonneg zero_le hn.ne').mp hs'.symm
  obtain ⟨lam, _, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_cartan hπ n g
  have ht : Δ (Iwasawa.torus T.uniformizerUnit lam) = 1 := by
    have hs := map_torus_of_commGroup Δu i0 T.uniformizerUnit lam
    have hd' : Δu (Iwasawa.diagonalUnits (Pi.mulSingle i0 T.uniformizerUnit)) = 1 :=
      Units.ext hd
    rw [hd', one_zpow] at hs
    exact congrArg (fun u : ℝ≥0ˣ => (u : ℝ≥0)) hs
  rw [map_mul, map_mul, hΔK k₁ hk₁, ht, hΔK k₂ hk₂, one_mul, one_mul]

/-- Every Haar measure on `GL_n` over a non-archimedean local field is right invariant. -/
theorem generalLinear_isMulRightInvariant (n : ℕ)
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  constructor
  intro g
  have h := map_mul_right_eq_modularCharacter_smul E n μ g
  rw [modularCharacterFun_generalLinear E n g, one_smul] at h
  exact h

end Local

end Langlands.BaseChange
