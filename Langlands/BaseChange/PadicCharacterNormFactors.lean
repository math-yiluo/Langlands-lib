import Langlands.BaseChange.PadicNormTwistFactorComparison
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Rank-one auxiliary factors for arbitrary characters under the norm -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Langlands.BaseChange

open HarmonicAnalysis LocalClassField
open LocalFactor.PadicAbelian (epsilonExponent lPolynomial)

universe u v

private theorem conductorZero_iff_unramified {p : ℕ} [Fact p.Prime]
    {K : PadicField p} (T : K.TopologicalData) :
    letI := T.topology
    ∀ (χ : Quasicharacter K.Carrier),
      T.multiplicativeConductor χ = 0 ↔ T.IsUnramifiedCharacter χ.toMonoidHom := by
  let := T.topology
  intro χ
  rw [T.multiplicativeConductor_eq_zero_iff, PadicField.TopologicalData.IsUnramifiedCharacter,
    ← T.ker_ordUnits]
  constructor
  · intro h a ha
    change T.ord (a : K.Carrier) = 0 at ha
    exact h a ((T.normalizedAbs_eq_one_iff_discreteValuation _).mp
      ((T.ord_eq_zero_iff_normalizedAbs a).mp ha))
  · intro h a ha
    apply h
    change T.ord (a : K.Carrier) = 0
    exact (T.ord_eq_zero_iff_normalizedAbs a).mpr
      ((T.normalizedAbs_eq_one_iff_discreteValuation _).mpr ha)

section Euler

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier]
  (T : F.TopologicalData) (S : E.TopologicalData)

private theorem unramifiedCharacter_norm_apply {f : ℕ}
    (hf : letI := T.valuativeRel; letI := S.valuativeRel; IsResidueDegree F.Carrier E.Carrier f)
    (z : ℂˣ) (x : E.Carrierˣ) :
    T.unramifiedCharacter z (localNorm T S x) = S.unramifiedCharacter (z ^ f) x := by
  rw [T.unramifiedCharacter_apply, S.unramifiedCharacter_apply,
    ord_localNorm_eq_residueDegree_mul T S hf, zpow_mul, zpow_natCast]

/-- The rank-one Euler comparison holds for every lower quasicharacter.
The upper polynomial uses the residue-degree substitution. -/
theorem prod_lPolynomial_normTwists {f : ℕ}
    (hf : letI := T.valuativeRel; letI := S.valuativeRel; IsResidueDegree F.Carrier E.Carrier f) :
    letI := T.topology
    letI := S.topology
    ∀ (χ : Quasicharacter F.Carrier)
      (A : Finset (F.Carrierˣ →* ℂˣ)), (∀ κ, κ ∈ A ↔ IsNormTrivial E.Carrier κ) →
    ∀ (ξ : A → Quasicharacter F.Carrier),
      (∀ κ, (ξ κ).toMonoidHom = κ.val * χ.toMonoidHom) →
      (∏ κ : A, lPolynomial T (ξ κ)) =
        expand ℂ f (lPolynomial S (χ.comp (localNorm T S))) := by
  classical
  let := T.topology
  let := S.topology
  intro χ A hA ξ hξ
  let η := χ.comp (localNorm T S)
  have hcomp (κ : A) (x : E.Carrierˣ) : ξ κ (localNorm T S x) = η x := by
    change (ξ κ).toMonoidHom (localNorm T S x) = χ.toMonoidHom (localNorm T S x)
    rw [hξ κ, MonoidHom.mul_apply]
    have hκ : κ.val (localNorm T S x) = 1 := (hA _).mp κ.property x
    rw [hκ, one_mul]
  by_cases hu : S.IsUnramifiedCharacter η.toMonoidHom
  · have hq : S.residueCardinality = T.residueCardinality ^ f := hf
    have hfpos : 0 < f := Nat.pos_of_ne_zero fun h =>
      S.residueCardinality_gt_one.ne' (by simpa [h] using hq)
    let c := η S.uniformizerUnit
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c : ℂ) hfpos
    have hz₀ : z ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by simpa [zero_pow hfpos.ne'] using hz.symm)
    let a := Units.mk0 z hz₀
    have ha : a ^ f = c := Units.ext (by simpa [a] using hz)
    let χ₀ := T.unramifiedCharacterContinuous a
    have hχ₀ (x : E.Carrierˣ) : χ₀ (localNorm T S x) = η x := by
      change T.unramifiedCharacter a (localNorm T S x) = η.toMonoidHom x
      rw [unramifiedCharacter_norm_apply T S hf, ha,
        congrArg (fun φ : E.Carrierˣ →* ℂˣ => φ x) (S.eq_unramifiedCharacter _ hu)]
      rfl
    let δ := χ.toMonoidHom * (χ₀.toMonoidHom)⁻¹
    have hδ : IsNormTrivial E.Carrier δ := by
      intro x
      change η x * (χ₀ (localNorm T S x))⁻¹ = 1
      rw [hχ₀, mul_inv_cancel]
    let e : A ≃ A :=
      { toFun := fun κ => ⟨κ.val * δ, (hA _).mpr (((hA _).mp κ.property).mul hδ)⟩
        invFun := fun κ => ⟨κ.val * δ⁻¹, (hA _).mpr (((hA _).mp κ.property).mul hδ.inv)⟩
        left_inv := fun κ => Subtype.ext (by
          change κ.val * δ * δ⁻¹ = κ.val
          ext x : 1
          simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_assoc, mul_inv_cancel, mul_one])
        right_inv := fun κ => Subtype.ext (by
          change κ.val * δ⁻¹ * δ = κ.val
          ext x : 1
          simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_assoc, inv_mul_cancel, mul_one]) }
    have he (κ : A) : (ξ (e.symm κ)).toMonoidHom = κ.val * χ₀.toMonoidHom := by
      rw [hξ]
      change (κ.val * δ⁻¹) * χ.toMonoidHom = _
      ext x : 1
      simp only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply]
      group
    have hη : χ₀.comp (localNorm T S) = η := ContinuousMonoidHom.ext hχ₀
    calc
      _ = ∏ κ : A, lPolynomial T (ξ (e.symm κ)) :=
        Fintype.prod_equiv e _ _ (fun κ => by simp)
      _ = expand ℂ f (lPolynomial S (χ₀.comp (localNorm T S))) :=
        prod_lPolynomial_unramifiedNormTwists T S hf χ₀ (T.isUnramifiedCharacter a) A hA
          (ξ ∘ e.symm) he
      _ = _ := by rw [hη]
  · have hl (κ : A) : T.multiplicativeConductor (ξ κ) ≠ 0 := by
      intro h
      have huκ := T.eq_unramifiedCharacter (ξ κ).toMonoidHom
        ((conductorZero_iff_unramified T _).mp h)
      apply hu
      have heq : η.toMonoidHom = S.unramifiedCharacter ((ξ κ T.uniformizerUnit) ^ f) := by
        ext x : 1
        rw [← unramifiedCharacter_norm_apply T S hf]
        exact (hcomp κ x).symm.trans (DFunLike.congr_fun huκ (localNorm T S x))
      rw [heq]
      exact S.isUnramifiedCharacter _
    have hη := mt (conductorZero_iff_unramified S η).mp hu
    change (∏ κ : A, lPolynomial T (ξ κ)) = expand ℂ f (lPolynomial S η)
    simp [lPolynomial, hl, hη]

end Euler

/-- The local norm comparison for rank-one Euler denominators and epsilon
exponents with an arbitrary quasicharacter and trace-related additive characters. -/
def PadicCharacterNormFactorsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] [IsAbelianGalois F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    letI := T.topology
    letI := S.topology
    letI := T.valuativeRel
    letI := S.valuativeRel
    ∀ [IsModuleTopology F.Carrier E.Carrier] (f d : ℕ),
      IsResidueDegree F.Carrier E.Carrier f → IsDifferentExponent F.Carrier E.Carrier d →
      ∀ (ψF : UnitaryAdditiveCharacter F.Carrier) (ψE : UnitaryAdditiveCharacter E.Carrier),
        (∀ x : E.Carrier, ψE x = ψF (Algebra.trace F.Carrier E.Carrier x)) →
      ∀ (χ : Quasicharacter F.Carrier)
        (A : Finset (F.Carrierˣ →* ℂˣ)), (∀ κ, κ ∈ A ↔ IsNormTrivial E.Carrier κ) →
      ∀ (ξ : A → Quasicharacter F.Carrier),
        (∀ κ, (ξ κ).toMonoidHom = κ.val * χ.toMonoidHom) →
        (∏ κ : A, lPolynomial T (ξ κ)) = expand ℂ f (lPolynomial S (χ.comp (localNorm T S))) ∧
        (∑ κ : A, epsilonExponent T (ξ κ) ψF) = (f : ℤ) * epsilonExponent S (χ.comp (localNorm T S)) ψE

theorem padicCharacterNormFactors : PadicCharacterNormFactorsStatement.{u, v} := by
  intro p _ F E _ _ _ _ T S
  let := T.topology
  let := S.topology
  let := T.valuativeRel
  let := S.valuativeRel
  let := T.localField
  let := S.localField
  intro _ f d hf hd ψF ψE htrace χ A hA ξ hξ
  refine ⟨prod_lPolynomial_normTwists T S hf χ A hA ξ hξ, ?_⟩
  obtain ⟨a, ha, hsum⟩ := padicNormPullbackConductor p F E T S χ f d hf hd A hA
  let η := χ.comp (localNorm T S)
  have hav (κ : A) : T.multiplicativeConductor (ξ κ) = a κ.val := by
    obtain ⟨ξ', hξ', hlevel⟩ := ha κ.val κ.property
    have heq : ξ κ = ξ' := ContinuousMonoidHom.toMonoidHom_injective ((hξ κ).trans hξ'.symm)
    have h : T.toLocalFieldData.multiplicativeConductor ξ' = a κ.val := hlevel
    rw [T.toLocalFieldData_multiplicativeConductor] at h
    simpa only [heq] using h
  have hsumNat : (∑ κ : A, T.multiplicativeConductor (ξ κ)) =
      f * (S.multiplicativeConductor η + d) := by
    rw [show (∑ κ : A, T.multiplicativeConductor (ξ κ)) = ∑ κ ∈ A, a κ by
      rw [← Finset.sum_coe_sort A a]
      exact Finset.sum_congr rfl fun κ _ => hav κ]
    change (∑ κ ∈ A, a κ) = f * (S.toLocalFieldData.multiplicativeConductor η + d) at hsum
    rwa [S.toLocalFieldData_multiplicativeConductor] at hsum
  have hsumInt : (∑ κ : A, (T.multiplicativeConductor (ξ κ) : ℤ)) =
      (f : ℤ) * ((S.multiplicativeConductor η : ℤ) + (d : ℤ)) := by exact_mod_cast hsumNat
  have hcard := card_of_mem_iff_isNormTrivial F E A hA
  have hcond := residueDegree_mul_additiveConductor_of_trace T S hf hd ψF ψE htrace
  change (∑ κ : A, epsilonExponent T (ξ κ) ψF) = (f : ℤ) * epsilonExponent S η ψE
  simp only [epsilonExponent, Finset.sum_add_distrib, hsumInt, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, hcard, nsmul_eq_mul]
  linear_combination -hcond

end Langlands.BaseChange
