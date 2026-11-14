import Langlands.Geometry.Building.Kottwitz.NormalizedValuationStatement
import Langlands.ClassFieldTheory.Local.SeparableInertiaNormProof
import Langlands.FieldTheory.HenselianDiscreteDimensionLEOneProof
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction

/-! # Integer normalization of the valuations on finite extensions of `K` -/

noncomputable section

universe u

open scoped NNReal WithZero

namespace Langlands.Geometry.Building.Kottwitz

open Langlands.ClassFieldTheory.Local.SeparableInertiaNorm
open Langlands.LocalGalois.Separable

/-! ### Generic integer normalization of real valuations -/

namespace IntegerNormalization

variable {R : Type*} [Field R]

/-- The comparison map `ℤᵐ⁰ → ℝ≥0` sends the integer `m` to `e ^ m`. -/
theorem toNNReal_coe_ofAdd {e : ℝ≥0} (he : e ≠ 0) (m : ℤ) :
    WithZeroMulInt.toNNReal he ((Multiplicative.ofAdd m : Multiplicative ℤ) : ℤᵐ⁰) = e ^ m := by
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.coe_ne_zero, WithZero.unzero_coe,
    toAdd_ofAdd]

/-- A real valuation whose nonzero values are integer powers of some `e > 1` is the composite of
an integer-valued valuation with `m ↦ e ^ m`. -/
theorem exists_intValuation_of_zpow (w : Valuation R ℝ≥0) {e : ℝ≥0} (he : 1 < e)
    (hdisc : ∀ x : R, x ≠ 0 → ∃ m : ℤ, w x = e ^ m) :
    ∃ v : Valuation R ℤᵐ⁰, ∀ x, WithZeroMulInt.toNNReal (ne_zero_of_lt he) (v x) = w x := by
  have hmono := WithZeroMulInt.toNNReal_strictMono he
  have hex : ∀ x : R, ∃ a : ℤᵐ⁰, WithZeroMulInt.toNNReal (ne_zero_of_lt he) a = w x := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by rw [hx, map_zero, map_zero]⟩
    · obtain ⟨m, hm⟩ := hdisc x hx
      exact ⟨((Multiplicative.ofAdd m : Multiplicative ℤ) : ℤᵐ⁰), by rw [toNNReal_coe_ofAdd, hm]⟩
  choose f hf using hex
  have hinj := hmono.injective
  refine ⟨{ toFun := f,
             map_zero' := hinj (by rw [hf, map_zero, map_zero]),
             map_one' := hinj (by rw [hf, map_one, map_one]),
             map_mul' := fun x y => hinj (by rw [hf, map_mul, map_mul, hf, hf]),
             map_add_le_max' := fun x y => hmono.le_iff_le.mp (by
               rw [hf, hmono.monotone.map_max, hf, hf]
               exact w.map_add x y) }, hf⟩

/-- A multiplicative map that compares values exactly like a valuation is itself a valuation. -/
def valuationOfLeIff {Γ₀ Γ₁ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    [LinearOrderedCommMonoidWithZero Γ₁] (w : Valuation R Γ₀) (f : R →*₀ Γ₁)
    (hf : ∀ x y, f x ≤ f y ↔ w x ≤ w y) : Valuation R Γ₁ where
  toMonoidWithZeroHom := f
  map_add_le_max' x y := by
    rcases le_total (w x) (w y) with h | h
    · exact ((hf (x + y) y).2 ((w.map_add x y).trans (max_le h le_rfl))).trans
        (le_max_right _ _)
    · exact ((hf (x + y) x).2 ((w.map_add x y).trans (max_le le_rfl h))).trans
        (le_max_left _ _)

theorem valuationOfLeIff_apply {Γ₀ Γ₁ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    [LinearOrderedCommMonoidWithZero Γ₁] (w : Valuation R Γ₀) (f : R →*₀ Γ₁)
    (hf : ∀ x y, f x ≤ f y ↔ w x ≤ w y) (x : R) : valuationOfLeIff w f hf x = f x := rfl

theorem valuationOfLeIff_isEquiv {Γ₀ Γ₁ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    [LinearOrderedCommMonoidWithZero Γ₁] (w : Valuation R Γ₀) (f : R →*₀ Γ₁)
    (hf : ∀ x y, f x ≤ f y ↔ w x ≤ w y) : (valuationOfLeIff w f hf).IsEquiv w :=
  fun x y => hf x y

/-- No element of `ℤᵐ⁰` lies strictly between the generator `ofAdd (-1)` and `1`. -/
theorem not_ofAdd_neg_one_lt_lt_one (a : ℤᵐ⁰)
    (h₁ : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) < a) (h₂ : a < 1) :
    False := by
  have ha : a ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le h₁)
  obtain ⟨b, rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  have h1 : (-1 : ℤ) < b.toAdd := Multiplicative.ofAdd_lt.mp (WithZero.coe_lt_coe.mp h₁)
  have h2 : b.toAdd < 0 := Multiplicative.ofAdd_lt.mp (WithZero.coe_lt_coe.mp h₂)
  omega

/-- Every nonzero element of `ℤᵐ⁰` is an integer power of the generator `ofAdd (-1)`. -/
theorem exists_eq_zpow_ofAdd_neg_one (a : ℤᵐ⁰) (ha : a ≠ 0) :
    ∃ m : ℤ, a = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) ^ m := by
  obtain ⟨b, rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  refine ⟨-b.toAdd, ?_⟩
  rw [← WithZero.coe_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_neg_one, neg_neg, ofAdd_toAdd]

/-- Two equivalent surjective `ℤᵐ⁰`-valued valuations are equal. -/
theorem eq_of_isEquiv_of_surjective (v₁ v₂ : Valuation R ℤᵐ⁰) (h : v₁.IsEquiv v₂)
    (h₁ : Function.Surjective v₁) (h₂ : Function.Surjective v₂) : v₁ = v₂ := by
  set g : ℤᵐ⁰ := ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) with hg
  have hg1 : g < 1 := by
    have : (Multiplicative.ofAdd (-1 : ℤ)) < 1 := Multiplicative.ofAdd_lt.mpr (by omega)
    exact WithZero.coe_lt_coe.mpr this
  obtain ⟨π, hπ⟩ := h₁ g
  obtain ⟨ρ, hρ⟩ := h₂ g
  have hπ2 : v₂ π = g := by
    rcases lt_trichotomy (v₂ π) g with hlt | heq | hgt
    · have hlt' : v₁ π < v₁ ρ := by
        apply h.lt_iff_lt.mpr
        rw [hρ]
        exact hlt
      have hρ1 : v₁ ρ < 1 := by
        apply h.lt_one_iff_lt_one.mpr
        rw [hρ]
        exact hg1
      rw [hπ] at hlt'
      exact (not_ofAdd_neg_one_lt_lt_one _ hlt' hρ1).elim
    · exact heq
    · have hπ1 : v₂ π < 1 := by
        apply h.lt_one_iff_lt_one.mp
        rw [hπ]
        exact hg1
      exact (not_ofAdd_neg_one_lt_lt_one _ hgt hπ1).elim
  ext x
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  obtain ⟨m, hm⟩ := exists_eq_zpow_ofAdd_neg_one (v₁ x) ((Valuation.ne_zero_iff _).mpr hx)
  have hxπ : v₁ x = v₁ (π ^ m) := by rw [map_zpow₀, hπ, hm]
  rw [h.eq_iff.mp hxπ, map_zpow₀, hπ2, hm]

end IntegerNormalization

open IntegerNormalization

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- KP's maximal unramified extension `K` satisfies the dimension-one norm criterion. -/
theorem unramifiedClosure_hasDimensionLEOne :
    Langlands.FieldTheory.HasDimensionLEOne (UnramifiedClosure F) :=
  Langlands.FieldTheory.henselianDiscreteDimensionLEOne (UnramifiedClosure F)
    (MaximalUnramified.valuation F) (MaximalUnramified.valuation_surjective F)
    (MaximalUnramified.valuationSubring_isHenselian F)
    (MaximalUnramified.residueField_isAlgClosed F)

/-- The spectral valuation is invariant under automorphisms over any intermediate field. -/
theorem sepClosureValuation_algEquiv
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    (σ : SeparableClosure F ≃ₐ[L] SeparableClosure F) (x : SeparableClosure F) :
    sepClosureValuation F (σ x) = sepClosureValuation F x :=
  (ambientHyp_sepClosureValuation F).inv_of σ x

/-- The spectral value of a relative norm is the power of the spectral value by the degree. -/
theorem intermediateValuation_norm
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] (x : L) :
    sepClosureValuation F (algebraMap (UnramifiedClosure F) (SeparableClosure F)
        (Algebra.norm (UnramifiedClosure F) x)) =
      intermediateValuation F L x ^ Module.finrank (UnramifiedClosure F) L :=
  val_norm_eq (fun σ y => (ambientHyp_sepClosureValuation F).inv σ y) x

/-- The spectral valuation on a finite extension of `K` has a uniformizer. -/
theorem exists_intermediateValUniformizer
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] :
    ∃ π : L, ValUniformizer (intermediateValuation F L) π := by
  obtain ⟨πK, hπ0, hπ1, hπK⟩ := (ambientHyp_sepClosureValuation F).unif
  set q := sepClosureValuation F (algebraMap (UnramifiedClosure F) (SeparableClosure F) πK)
  have hn : 0 < Module.finrank (UnramifiedClosure F) L := Module.finrank_pos
  refine exists_valUniformizer (D := Module.finrank (UnramifiedClosure F) L) hn
    (q := q) hπ0 hπ1 (fun x hx0 hx1 => ?_)
    (c := algebraMap (UnramifiedClosure F) L πK) ?_ ?_
  · have hN0 : Algebra.norm (UnramifiedClosure F) x ≠ 0 :=
      (Algebra.norm_ne_zero_iff).mpr hx0
    obtain ⟨k, hk⟩ := hπK (Algebra.norm (UnramifiedClosure F) x) hN0 (by
      change sepClosureValuation F _ ≤ 1
      rw [intermediateValuation_norm]
      exact pow_le_one₀ zero_le hx1)
    refine ⟨k, ?_⟩
    rw [← intermediateValuation_norm]
    exact hk
  · exact hπ0
  · exact hπ1

/-- Existence of the integer normalization. -/
theorem exists_isNormalizedIntermediateValuation
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] :
    ∃ v, IsNormalizedIntermediateValuation F L v := by
  obtain ⟨π, hπ0, hπ1, hπ⟩ := exists_intermediateValUniformizer F L
  set γ := intermediateValuation F L π
  have he : 1 < γ⁻¹ := one_lt_inv₀ hπ0 |>.mpr hπ1
  have hdisc : ∀ x : L, x ≠ 0 → ∃ m : ℤ, intermediateValuation F L x = γ⁻¹ ^ m := by
    intro x hx
    rcases le_total (intermediateValuation F L x) 1 with h | h
    · obtain ⟨k, hk⟩ := hπ x hx h
      exact ⟨-(k : ℤ), by rw [hk, zpow_neg, inv_zpow, inv_inv, zpow_natCast]⟩
    · have hxi : intermediateValuation F L x⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ h
      obtain ⟨k, hk⟩ := hπ x⁻¹ (inv_ne_zero hx) hxi
      refine ⟨k, ?_⟩
      rw [← inv_inv (intermediateValuation F L x), ← map_inv₀, hk, inv_zpow', zpow_neg,
        zpow_natCast]
  obtain ⟨v, hv⟩ := exists_intValuation_of_zpow (intermediateValuation F L) he hdisc
  have hmono := WithZeroMulInt.toNNReal_strictMono he
  refine ⟨v, fun x y => by rw [← hv, ← hv]; exact hmono.le_iff_le.symm, fun a => ?_⟩
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha, map_zero]⟩
  obtain ⟨b, rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  refine ⟨π ^ (-b.toAdd), hmono.injective ?_⟩
  rw [hv, map_zpow₀,
    show ((b : ℤᵐ⁰)) = ((Multiplicative.ofAdd b.toAdd : Multiplicative ℤ) : ℤᵐ⁰) from rfl,
    toNNReal_coe_ofAdd, zpow_neg, ← inv_zpow]

/-- KP's integer normalization exists and is unique. -/
theorem normalizedIntermediateValuationStatement :
    NormalizedIntermediateValuationStatement.{u} := by
  intro F _ _ _ _ L _
  obtain ⟨v, hv⟩ := exists_isNormalizedIntermediateValuation F L
  exact ⟨v, hv, fun v' hv' =>
    eq_of_isEquiv_of_surjective v' v (hv'.1.trans hv.1.symm) hv'.2 hv.2⟩

/-- The selected integer normalization has its defining property. -/
theorem normalizedIntermediateValuation_spec'
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] :
    IsNormalizedIntermediateValuation F L (normalizedIntermediateValuation F L) :=
  normalizedIntermediateValuation_spec F L (exists_isNormalizedIntermediateValuation F L)

/-- A normalized valuation is the selected one. -/
theorem eq_normalizedIntermediateValuation
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] {v : Valuation L ℤᵐ⁰}
    (hv : IsNormalizedIntermediateValuation F L v) : v = normalizedIntermediateValuation F L :=
  eq_of_isEquiv_of_surjective _ _ (hv.1.trans (normalizedIntermediateValuation_spec' F L).1.symm)
    hv.2 (normalizedIntermediateValuation_spec' F L).2

/-- The integer normalization is invariant under `Gal(L/K)`. -/
theorem normalizedIntermediateValuation_algEquiv
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L]
    (σ : L ≃ₐ[UnramifiedClosure F] L) (x : L) :
    normalizedIntermediateValuation F L (σ x) = normalizedIntermediateValuation F L x := by
  have hw : intermediateValuation F L (σ x) = intermediateValuation F L x := by
    change sepClosureValuation F (algebraMap L (SeparableClosure F) (σ x)) =
      sepClosureValuation F (algebraMap L (SeparableClosure F) x)
    rw [← AlgEquiv.liftNormal_commutes σ (SeparableClosure F) x]
    exact (ambientHyp_sepClosureValuation F).inv _ _
  exact (normalizedIntermediateValuation_spec' F L).1.eq_iff.mpr hw

/-- For finite extensions `L ≤ M` of `K`, every nonzero element of `L` is a norm from `M`:
pass to the Galois closure of `M` over `K` and use the dimension-one norm criterion. -/
theorem exists_norm_eq_of_le
    (L M : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [FiniteDimensional (UnramifiedClosure F) M]
    (h : L ≤ M) (y : L) (hy : y ≠ 0) :
    letI : Algebra L M := (IntermediateField.inclusion h).toAlgebra
    ∃ x : M, Algebra.norm L x = y := by
  let : Algebra L M := (IntermediateField.inclusion h).toAlgebra
  let : Module L M := Algebra.toModule
  let M' := IntermediateField.normalClosure (UnramifiedClosure F) M (SeparableClosure F)
  have hMM' : M ≤ M' := IntermediateField.le_normalClosure M
  have hLM' : L ≤ M' := h.trans hMM'
  let : Algebra L M' := (IntermediateField.inclusion hLM').toAlgebra
  let : Module L M' := Algebra.toModule
  let : Algebra M M' := (IntermediateField.inclusion hMM').toAlgebra
  let : Module M M' := Algebra.toModule
  have : IsScalarTower L M M' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower (UnramifiedClosure F) L M' :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FiniteDimensional L M' := FiniteDimensional.right (UnramifiedClosure F) L M'
  have : IsGalois L M' := IsGalois.tower_top_of_isGalois (UnramifiedClosure F) L M'
  have : Algebra.IsSeparable (UnramifiedClosure F) L :=
    Algebra.isSeparable_tower_bot_of_isSeparable (UnramifiedClosure F) L (SeparableClosure F)
  obtain ⟨z, hz⟩ := unramifiedClosure_hasDimensionLEOne F L M' (Units.mk0 y hy)
  refine ⟨Algebra.norm M (z : M'), ?_⟩
  rw [Algebra.norm_norm]
  exact congrArg Units.val hz

/-- The integer normalizations are compatible with norms: if `L ≤ M` are finite over `K`, then
`v_L (N_{M/L} x) = v_M x`. -/
theorem normalizedIntermediateValuation_norm
    (L M : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [FiniteDimensional (UnramifiedClosure F) M]
    (h : L ≤ M) (x : M) :
    letI : Algebra L M := (IntermediateField.inclusion h).toAlgebra
    normalizedIntermediateValuation F L (Algebra.norm L x) =
      normalizedIntermediateValuation F M x := by
  let : Algebra L M := (IntermediateField.inclusion h).toAlgebra
  let : Module L M := Algebra.toModule
  have : IsScalarTower L M (SeparableClosure F) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower (UnramifiedClosure F) L M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FiniteDimensional L M := FiniteDimensional.right (UnramifiedClosure F) L M
  have hd : Module.finrank L M ≠ 0 := Module.finrank_pos.ne'
  have hnorm : ∀ y : M, intermediateValuation F L (Algebra.norm L y) =
      intermediateValuation F M y ^ Module.finrank L M := fun y =>
    val_norm_eq (fun σ z => sepClosureValuation_algEquiv F L σ z) y
  have hL := normalizedIntermediateValuation_spec' F L
  let f : M →*₀ ℤᵐ⁰ :=
    { toFun := fun y => normalizedIntermediateValuation F L (Algebra.norm L y)
      map_zero' := by rw [Algebra.norm_zero, map_zero]
      map_one' := by rw [map_one, map_one]
      map_mul' := fun y z => by rw [map_mul, map_mul] }
  have hf : ∀ y z, f y ≤ f z ↔ intermediateValuation F M y ≤ intermediateValuation F M z := by
    intro y z
    change normalizedIntermediateValuation F L _ ≤ normalizedIntermediateValuation F L _ ↔ _
    rw [hL.1 _ _, hnorm, hnorm]
    exact pow_le_pow_iff_left₀ zero_le zero_le hd
  have hu : IsNormalizedIntermediateValuation F M (valuationOfLeIff _ f hf) := by
    refine ⟨valuationOfLeIff_isEquiv _ _ _, fun a => ?_⟩
    obtain ⟨y, hy⟩ := hL.2 a
    by_cases hy0 : y = 0
    · refine ⟨0, ?_⟩
      rw [map_zero, ← hy, hy0, map_zero]
    obtain ⟨z, hz⟩ := exists_norm_eq_of_le F L M h y hy0
    refine ⟨z, ?_⟩
    change normalizedIntermediateValuation F L (Algebra.norm L z) = a
    rw [hz, hy]
  rw [← eq_normalizedIntermediateValuation F M hu]
  rfl

end Langlands.Geometry.Building.Kottwitz
