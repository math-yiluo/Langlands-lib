import Langlands.Galois.Local.SeparableHenselian
import Langlands.Galois.Local.SeparableValueArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.AdjoinRoot

noncomputable section

open Polynomial IsLocalRing ValuativeRel
open scoped NNReal IntermediateField

namespace Langlands.LocalGalois.Separable

universe u

/-! ### Generic lemmas -/

section Generic

/-- Two `k`-th roots of unity congruent modulo the maximal ideal agree when `k` is a unit. -/
theorem eq_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsLocalRing R] {k : ℕ}
    (hk : IsUnit (k : R)) {a b : R} (ha : a ^ k = 1) (hb : b ^ k = 1)
    (hab : a - b ∈ maximalIdeal R) : a = b := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := X ^ k - 1) ?_ ?_ hab ?_
  · simp [ha]
  · simp [hb]
  · simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul, eval_C,
      eval_pow, eval_X]
    exact hk.mul ((IsUnit.of_pow_eq_one ha hk0).pow _)

/-- A nonzero element integral over a finite field is a `(card ^ d - 1)`-th root of unity. -/
theorem exists_pow_card_pow_sub_one_eq_one {k L : Type*} [Field k] [Finite k] [Field L]
    [Algebra k L] {z : L} (hz : IsIntegral k z) (hz0 : z ≠ 0) :
    ∃ d, 0 < d ∧ z ^ (Nat.card k ^ d - 1) = 1 := by
  have : FiniteDimensional k k⟮z⟯ := IntermediateField.adjoin.finiteDimensional hz
  have : Finite k⟮z⟯ := Module.finite_of_finite k
  let : Fintype k⟮z⟯ := Fintype.ofFinite _
  refine ⟨Module.finrank k k⟮z⟯, Module.finrank_pos, ?_⟩
  have hcard : Nat.card k⟮z⟯ = Nat.card k ^ Module.finrank k k⟮z⟯ :=
    Module.natCard_eq_pow_finrank
  have hne : (⟨z, IntermediateField.mem_adjoin_simple_self k z⟩ : k⟮z⟯) ≠ 0 := by
    intro h
    exact hz0 (congrArg Subtype.val h)
  have h := FiniteField.pow_card_sub_one_eq_one _ hne
  rw [Fintype.card_eq_nat_card, hcard] at h
  exact congrArg Subtype.val h

/-- Membership in the maximal ideal of a valuation subring is detected by the valuation. -/
theorem mem_maximalIdeal_iff_lt {K : Type*} [Field K] (v : Valuation K ℝ≥0)
    (x : v.valuationSubring) : x ∈ maximalIdeal v.valuationSubring ↔ v (x : K) < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers v).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, ne_of_lt⟩

theorem isUnit_iff_eq_one {K : Type*} [Field K] (v : Valuation K ℝ≥0)
    (x : v.valuationSubring) : IsUnit x ↔ v (x : K) = 1 :=
  (Valuation.integer.integers v).isUnit_iff_valuation_eq_one

end Generic

/-! ### Teichmüller roots of unity in the separable closure -/

section Arithmetic

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance arithNormedField : NontriviallyNormedField F := localNormedField F
local instance arithUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance arithComplete : CompleteSpace F := localNormedField_complete F
local instance arithResidueFinite : Finite (ResidueField (baseIntegers F)) :=
  localResidue_finite F

local notation "Ω" => SeparableClosure F
local notation "𝔸" => extensionIntegers F (SeparableClosure F)
local notation "κ" => ResidueField (baseIntegers F)

/-- `q ^ M - 1` is a unit in the integers of the separable closure, `q` the residue
cardinality. -/
theorem teichOrder_isUnit {M : ℕ} (hM : 0 < M) :
    IsUnit ((Nat.card κ ^ M - 1 : ℕ) : 𝔸) := by
  have hq : (Nat.card κ : κ) = 0 := by
    have := Fintype.ofFinite κ
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero κ
  have hpos : 1 ≤ Nat.card κ ^ M := Nat.one_le_pow _ _ Nat.card_pos
  rw [← residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_one]
  have h : (Nat.card κ : ResidueField 𝔸) = 0 := by
    rw [← map_natCast (algebraMap κ (ResidueField 𝔸)), hq, map_zero]
  rw [h, zero_pow hM.ne', zero_sub, neg_ne_zero]
  exact one_ne_zero

theorem teichOrder_ne_zero {M : ℕ} (hM : 0 < M) : Nat.card κ ^ M - 1 ≠ 0 := by
  intro h
  have := teichOrder_isUnit F hM
  rw [h, Nat.cast_zero] at this
  exact not_isUnit_zero this

theorem mem_integers_of_pow_eq_one {x : Ω} {k : ℕ} (hk : k ≠ 0) (hx : x ^ k = 1) :
    x ∈ 𝔸 := by
  rw [Valuation.mem_valuationSubring_iff]
  by_contra h
  push Not at h
  have := one_lt_pow₀ h hk
  rw [← map_pow, hx, map_one] at this
  exact lt_irrefl _ this

/-- Roots of unity of order `q ^ M - 1` are fixed by the inertia group. -/
theorem mem_inertiaFixedField_of_pow_eq_one {M : ℕ} (hM : 0 < M) (x : 𝔸)
    (hx : x ^ (Nat.card κ ^ M - 1) = 1) : (x : Ω) ∈ inertiaFixedField F := by
  rw [mem_inertiaFixedField_iff]
  intro σ hσ
  have h := (mem_separableInertia_iff F σ).mp hσ x
  have hσx : (integerAut F Ω σ x) ^ (Nat.card κ ^ M - 1) = 1 := by
    rw [← map_pow, hx, map_one]
  have := eq_of_pow_eq_one_of_sub_mem (teichOrder_isUnit F hM) hσx hx
    (by rw [← residue_eq_zero_iff, map_sub, h, sub_self])
  exact congrArg Subtype.val this

/-- Existence of a primitive root of unity of order `q ^ M - 1` in the integers. -/
theorem exists_teich {M : ℕ} (hM : 0 < M) :
    ∃ ζ : 𝔸, IsPrimitiveRoot ζ (Nat.card κ ^ M - 1) := by
  have hk := teichOrder_ne_zero F hM
  have : NeZero (((Nat.card κ ^ M - 1 : ℕ)) : Ω) := ⟨by
    intro h
    apply (teichOrder_isUnit F hM).ne_zero
    apply Subtype.ext
    simpa using h⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (Nat.card κ ^ M - 1)
  refine ⟨⟨ζ, mem_integers_of_pow_eq_one F hk hζ.pow_eq_one⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := (𝔸).subtype) hζ Subtype.val_injective

/-- The residue of a primitive Teichmüller root of unity is primitive. -/
theorem isPrimitiveRoot_residue {M : ℕ} (hM : 0 < M) {ζ : 𝔸}
    (hζ : IsPrimitiveRoot ζ (Nat.card κ ^ M - 1)) :
    IsPrimitiveRoot (residue 𝔸 ζ) (Nat.card κ ^ M - 1) := by
  refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl => ?_⟩
  apply hζ.dvd_of_pow_eq_one
  apply eq_of_pow_eq_one_of_sub_mem (teichOrder_isUnit F hM) _ (one_pow _)
  · rw [← residue_eq_zero_iff, map_sub, map_pow, hl, map_one, sub_self]
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem coe_pow_eq_one {ζ : 𝔸} {k : ℕ} (h : ζ ^ k = 1) : (ζ : Ω) ^ k = 1 := by
  simpa using congrArg ((↑) : 𝔸 → Ω) h

/-! ### The inertia fixed field is generated by Teichmüller roots of unity -/

/-- The roots of unity of order `q ^ M - 1`, `M > 0`, in the separable closure. -/
def teichSet : Set Ω := {x | ∃ M, 0 < M ∧ x ^ (Nat.card κ ^ M - 1) = 1}

/-- An automorphism fixing every Teichmüller root of unity lies in the inertia group. -/
theorem mem_separableInertia_of_forall_teichSet (σ : Gal(SeparableClosure F/F))
    (hσ : ∀ x ∈ teichSet F, σ x = x) : σ ∈ separableInertia F := by
  rw [mem_separableInertia_iff]
  intro x
  rw [← residueHom_apply]
  by_cases h0 : residue 𝔸 x = 0
  · rw [h0, map_zero]
  obtain ⟨d, hd, hz⟩ := exists_pow_card_pow_sub_one_eq_one
    (Algebra.IsIntegral.isIntegral (R := κ) (residue 𝔸 x)) h0
  obtain ⟨ζ, hζ⟩ := exists_teich F hd
  have : NeZero (Nat.card κ ^ d - 1) := ⟨teichOrder_ne_zero F hd⟩
  obtain ⟨i, -, hi⟩ := (isPrimitiveRoot_residue F hd hζ).eq_pow_of_pow_eq_one hz
  have hfix : integerAut F Ω σ ζ = ζ :=
    Subtype.ext (hσ _ ⟨d, hd, coe_pow_eq_one F hζ.pow_eq_one⟩)
  rw [← hi, map_pow, residueHom_apply, hfix]

theorem inertiaFixedField_le_adjoin :
    inertiaFixedField F ≤ IntermediateField.adjoin F (teichSet F) := by
  intro x hx
  rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin F (teichSet F)),
    IntermediateField.mem_fixedField_iff]
  intro σ hσ
  refine (mem_inertiaFixedField_iff F x).mp hx σ
    (mem_separableInertia_of_forall_teichSet F σ fun y hy => ?_)
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ y
    (IntermediateField.subset_adjoin F _ hy)

/-- Finitely many Teichmüller roots of unity have a common order `q ^ M - 1`. -/
theorem exists_common_teich (S : Finset Ω) (hS : (S : Set Ω) ⊆ teichSet F) :
    ∃ M, 0 < M ∧ ∀ y ∈ S, y ^ (Nat.card κ ^ M - 1) = 1 := by
  classical
  have hdvd : ∀ m n : ℕ, Nat.card κ ^ m - 1 ∣ Nat.card κ ^ (m * n) - 1 := fun m n => by
    simpa only [one_pow, pow_mul] using Nat.sub_dvd_pow_sub_pow (Nat.card κ ^ m) 1 n
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S ha ih =>
    obtain ⟨M₁, hM₁, h₁⟩ := hS (Finset.mem_insert_self a S)
    obtain ⟨M₂, hM₂, h₂⟩ := ih (fun y hy => hS (Finset.mem_insert_of_mem hy))
    refine ⟨M₁ * M₂, Nat.mul_pos hM₁ hM₂, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · obtain ⟨c, hc⟩ := hdvd M₁ M₂
      rw [hc, pow_mul, h₁, one_pow]
    · obtain ⟨c, hc⟩ := hdvd M₂ M₁
      rw [mul_comm M₁, hc, pow_mul, h₂ y hy, one_pow]

theorem mem_adjoin_of_pow_eq_one {M : ℕ} (hM : 0 < M) {ζ : 𝔸}
    (hζ : IsPrimitiveRoot ζ (Nat.card κ ^ M - 1)) {y : Ω}
    (hy : y ^ (Nat.card κ ^ M - 1) = 1) : y ∈ F⟮(ζ : Ω)⟯ := by
  have : NeZero (Nat.card κ ^ M - 1) := ⟨teichOrder_ne_zero F hM⟩
  have hζ' : IsPrimitiveRoot (ζ : Ω) (Nat.card κ ^ M - 1) :=
    hζ.map_of_injective (f := (𝔸).subtype) Subtype.val_injective
  obtain ⟨i, -, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hy
  exact pow_mem (IntermediateField.mem_adjoin_simple_self F _) i

/-- Every element of the inertia fixed field lies in `F(ζ)` for a Teichmüller root `ζ`. -/
theorem exists_teich_of_mem_inertiaFixedField {x : Ω} (hx : x ∈ inertiaFixedField F) :
    ∃ M, 0 < M ∧ ∃ ζ : 𝔸, IsPrimitiveRoot ζ (Nat.card κ ^ M - 1) ∧ x ∈ F⟮(ζ : Ω)⟯ := by
  obtain ⟨S, hS, hxS⟩ := IntermediateField.exists_finset_of_mem_adjoin
    (inertiaFixedField_le_adjoin F hx)
  obtain ⟨M, hM, hSM⟩ := exists_common_teich F S hS
  obtain ⟨ζ, hζ⟩ := exists_teich F hM
  refine ⟨M, hM, ζ, hζ, ?_⟩
  refine (IntermediateField.adjoin_le_iff.mpr ?_) hxS
  intro y hy
  exact mem_adjoin_of_pow_eq_one F hM hζ (hSM y hy)

/-! ### Degree comparison and values on `F(ζ)` -/

/-- The degree of a Teichmüller root over `F` is at most that of its residue over `κ`. -/
theorem natDegree_minpoly_le {M : ℕ} (hM : 0 < M) {ζ : 𝔸}
    (hζ : IsPrimitiveRoot ζ (Nat.card κ ^ M - 1)) :
    (minpoly F (ζ : Ω)).natDegree ≤ (minpoly κ (residue 𝔸 ζ)).natDegree := by
  classical
  let g : Ω → ResidueField 𝔸 := fun β => if h : β ∈ 𝔸 then residue 𝔸 ⟨β, h⟩ else 0
  have hg : ∀ σ : Gal(SeparableClosure F/F), g (σ (ζ : Ω)) = residue 𝔸 (integerAut F Ω σ ζ) :=
    fun σ => by
      simp only [g]
      exact dite_eq_left_of_eq_true (eq_true (integerAut F Ω σ ζ).2)
  have hroot : ∀ β ∈ (minpoly F (ζ : Ω)).rootSet Ω,
      ∃ σ : Gal(SeparableClosure F/F), σ (ζ : Ω) = β := fun β hβ =>
    minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _) (mem_rootSet'.mp hβ).2
  have hpow : ∀ σ : Gal(SeparableClosure F/F),
      (integerAut F Ω σ ζ) ^ (Nat.card κ ^ M - 1) = 1 := fun σ => by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  have hcard : ((minpoly F (ζ : Ω)).rootSet Ω).ncard = (minpoly F (ζ : Ω)).natDegree := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact card_rootSet_eq_natDegree (Algebra.IsSeparable.isSeparable F _)
      (Normal.splits inferInstance _)
  have hint : IsIntegral κ (residue 𝔸 ζ) := Algebra.IsIntegral.isIntegral _
  rw [← hcard]
  refine le_trans ?_ (ncard_rootSet_le (minpoly κ (residue 𝔸 ζ)) (ResidueField 𝔸))
  refine Set.ncard_le_ncard_of_injOn g ?_ ?_ (rootSet_finite _ _)
  · intro β hβ
    obtain ⟨σ, rfl⟩ := hroot β hβ
    rw [hg, ← residueHom_apply, mem_rootSet']
    refine ⟨Polynomial.map_ne_zero (minpoly.ne_zero hint), ?_⟩
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  · intro β₁ h₁ β₂ h₂ heq
    obtain ⟨σ₁, rfl⟩ := hroot β₁ h₁
    obtain ⟨σ₂, rfl⟩ := hroot β₂ h₂
    rw [hg, hg] at heq
    have := eq_of_pow_eq_one_of_sub_mem (teichOrder_isUnit F hM) (hpow σ₁) (hpow σ₂)
      (by rw [← residue_eq_zero_iff, map_sub, heq, sub_self])
    exact congrArg Subtype.val this

/-- A polynomial expression in a Teichmüller root of degree below its degree over `F` has
the value of its largest coefficient. -/
theorem exists_sepClosureValuation_aeval_eq {M : ℕ} (hM : 0 < M) {ζ : 𝔸}
    (hζ : IsPrimitiveRoot ζ (Nat.card κ ^ M - 1)) (f : F[X])
    (hf : f.natDegree < (minpoly F (ζ : Ω)).natDegree) :
    ∃ a : F, sepClosureValuation F (aeval (ζ : Ω) f) = ‖a‖₊ := by
  by_cases hf0 : f = 0
  · exact ⟨0, by simp [hf0]⟩
  obtain ⟨j, hj, hmax⟩ := f.support.exists_max_image (fun i => ‖f.coeff i‖)
    (nonempty_support_iff.mpr hf0)
  have hc : f.coeff j ≠ 0 := mem_support_iff.mp hj
  refine ⟨f.coeff j, ?_⟩
  have hlift : ∀ i, (C (f.coeff j)⁻¹ * f).coeff i ∈
      Set.range (algebraMap (baseIntegers F) F) := by
    intro i
    refine ⟨⟨(C (f.coeff j)⁻¹ * f).coeff i, ?_⟩, rfl⟩
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, coeff_C_mul]
    by_cases hi : i ∈ f.support
    · rw [nnnorm_mul, nnnorm_inv]
      refine inv_mul_le_one_of_le₀ ?_ (by positivity)
      exact hmax i hi
    · rw [notMem_support_iff.mp hi, mul_zero, nnnorm_zero]
      exact zero_le_one
  obtain ⟨g₀, hg₀⟩ := (mem_lifts _).mp ((lifts_iff_coeff_lifts _).mpr hlift)
  have hinj : Function.Injective (algebraMap (baseIntegers F) F) := Subtype.val_injective
  have hcoeff : g₀.coeff j = 1 := by
    apply hinj
    rw [← coeff_map, hg₀, coeff_C_mul, inv_mul_cancel₀ hc, map_one]
  have hdeg : g₀.natDegree < (minpoly F (ζ : Ω)).natDegree := by
    rw [← natDegree_map_eq_of_injective hinj, hg₀]
    exact lt_of_le_of_lt (natDegree_C_mul_le _ _) hf
  -- the residue of `g₀(ζ)` is a nonzero value of a polynomial of small degree
  have hcomp : (algebraMap κ (ResidueField 𝔸)).comp (residue (baseIntegers F)) =
      (residue 𝔸).comp (algebraMap (baseIntegers F) 𝔸) := RingHom.ext fun _ => rfl
  have hres : residue 𝔸 (aeval ζ g₀) = aeval (residue 𝔸 ζ) (g₀.map (residue (baseIntegers F))) := by
    rw [aeval_def, aeval_def, eval₂_map, hcomp, hom_eval₂]
  have hne : g₀.map (residue (baseIntegers F)) ≠ 0 := by
    intro h
    have := congrArg (fun p => p.coeff j) h
    simp only [coeff_map, hcoeff, map_one, coeff_zero] at this
    exact one_ne_zero this
  have hunit : IsUnit (aeval ζ g₀) := by
    rw [← residue_ne_zero_iff_isUnit, hres]
    intro h0
    have h1 := natDegree_le_natDegree (minpoly.degree_le_of_ne_zero κ (residue 𝔸 ζ) hne h0)
    have h2 := natDegree_map_le (f := residue (baseIntegers F)) (p := g₀)
    have h3 := natDegree_minpoly_le F hM hζ
    omega
  have hval : sepClosureValuation F ((aeval ζ g₀ : 𝔸) : Ω) = 1 :=
    (isUnit_iff_eq_one _ _).mp hunit
  have hcoe : ((aeval ζ g₀ : 𝔸) : Ω) = aeval (ζ : Ω) (C (f.coeff j)⁻¹ * f) := by
    have hc' : ((𝔸).subtype : 𝔸 →+* Ω).comp (algebraMap (baseIntegers F) 𝔸) =
        (algebraMap F Ω).comp (algebraMap (baseIntegers F) F) := RingHom.ext fun _ => rfl
    rw [← hg₀, aeval_def, aeval_def, eval₂_map, ← hc']
    exact hom_eval₂ g₀ (algebraMap (baseIntegers F) 𝔸) ((𝔸).subtype : 𝔸 →+* Ω) ζ
  have hf' : f = C (f.coeff j) * (C (f.coeff j)⁻¹ * f) := by
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  have hsplit : aeval (ζ : Ω) f =
      algebraMap F Ω (f.coeff j) * aeval (ζ : Ω) (C (f.coeff j)⁻¹ * f) := by
    conv_lhs => rw [hf']
    rw [map_mul, aeval_C]
  rw [hsplit, map_mul, ← hcoe, hval, mul_one]
  exact NNReal.eq (spectralNorm_extends (K := F) (L := Ω) (f.coeff j))

/-- **Values.** Every value of the inertia fixed field is a value of the base. -/
theorem fixedFieldValuesFromBase : FixedFieldValuesFromBase F := by
  intro x
  obtain ⟨M, hM, ζ, hζ, hx⟩ := exists_teich_of_mem_inertiaFixedField F x.2
  have hint : IsIntegral F (ζ : Ω) := Algebra.IsIntegral.isIntegral _
  obtain ⟨f, hfdeg, hf⟩ :=
    (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval ⟨x, hx⟩
  have hx' : (x : Ω) = aeval (ζ : Ω) f := by
    have := congrArg Subtype.val hf
    rwa [IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.AdjoinSimple.coe_aeval_gen_apply] at this
  obtain ⟨a, ha⟩ := exists_sepClosureValuation_aeval_eq F hM hζ f hfdeg
  exact ⟨a, by rw [fixedFieldValuation_apply, hx', ha]⟩

/-! ### The residue field of the inertia fixed field -/

local notation "𝔹" => fixedFieldIntegers F

/-- Every nonzero residue of the inertia fixed field is a root of unity of order
`q ^ d - 1` for some `d > 0`. -/
theorem exists_residue_pow_eq_one {r : ResidueField 𝔹} (hr : r ≠ 0) :
    ∃ d, 0 < d ∧ r ^ (Nat.card κ ^ d - 1) = 1 := by
  let s : ResidueField 𝔸 := fixedFieldResidueInclusion F r
  have hs0 : s ≠ 0 := (_root_.map_ne_zero _).mpr hr
  obtain ⟨d, hd, h⟩ := exists_pow_card_pow_sub_one_eq_one
    (Algebra.IsIntegral.isIntegral (R := κ) s) hs0
  refine ⟨d, hd, (fixedFieldResidueInclusion F).injective ?_⟩
  rw [map_pow, map_one]
  exact h

/-- The residue field of the inertia fixed field contains a primitive root of unity of every
order `q ^ M - 1`, `M > 0`: the residue of a Teichmüller root of unity. -/
theorem exists_isPrimitiveRoot_residue {M : ℕ} (hM : 0 < M) :
    ∃ z : 𝔹, IsPrimitiveRoot (residue 𝔹 z) (Nat.card κ ^ M - 1) := by
  obtain ⟨ζ, hζ⟩ := exists_teich F hM
  have hU := mem_inertiaFixedField_of_pow_eq_one F hM ζ hζ.pow_eq_one
  have hval : fixedFieldValuation F ⟨(ζ : Ω), hU⟩ ≤ 1 := ζ.2
  let z : 𝔹 := ⟨⟨(ζ : Ω), hU⟩, hval⟩
  refine ⟨z, IsPrimitiveRoot.of_map_of_injective (f := fixedFieldResidueInclusion F) ?_
    (fixedFieldResidueInclusion F).injective⟩
  have hz : fixedFieldResidueInclusion F (residue 𝔹 z) = residue 𝔸 ζ := by
    rw [fixedFieldResidueInclusion_residue]
    rfl
  rw [hz]
  exact isPrimitiveRoot_residue F hM hζ

/-- **Residue field.** The residue field of the inertia fixed field is an algebraic closure
of the residue field of `F`. -/
theorem fixedFieldResidueIsAlgClosure : FixedFieldResidueIsAlgClosure F := by
  let := (residueToFixedField F).toAlgebra
  have hcard : Nat.card 𝓀[F] = Nat.card κ := Nat.card_congr (localResidueEquiv F).symm.toEquiv
  have hint : Algebra.IsIntegral 𝓀[F] (ResidueField 𝔹) := by
    refine ⟨fun r => ?_⟩
    by_cases hr : r = 0
    · rw [hr]
      exact isIntegral_zero
    obtain ⟨d, hd, h⟩ := exists_residue_pow_eq_one F hr
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero (teichOrder_ne_zero F hd)) ?_
    rw [h]
    exact isIntegral_one
  refine ⟨IsAlgClosed.of_exists_root _ fun p hmonic hirr => ?_, inferInstance⟩
  have := Fact.mk hirr
  -- a root `y` of `p` in the residue field gives a root in the residue field
  have hof : ∀ y, AdjoinRoot.root p = AdjoinRoot.of p y → ∃ x, p.eval x = 0 := by
    intro y hy
    refine ⟨y, (map_eq_zero_iff _ (AdjoinRoot.of p).injective).mp ?_⟩
    rw [← eval₂_hom, ← hy]
    exact AdjoinRoot.eval₂_root p
  by_cases h0 : AdjoinRoot.root p = 0
  · exact hof 0 (by rw [h0, map_zero])
  have hr : IsIntegral 𝓀[F] (AdjoinRoot.root p) :=
    isIntegral_trans (R := 𝓀[F]) (A := ResidueField 𝔹) _
      (AdjoinRoot.isIntegral_root hirr.ne_zero)
  obtain ⟨d, hd, h⟩ := exists_pow_card_pow_sub_one_eq_one hr h0
  rw [hcard] at h
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot_residue F hd
  have : NeZero (Nat.card κ ^ d - 1) := ⟨teichOrder_ne_zero F hd⟩
  obtain ⟨i, -, hi⟩ := (hz.map_of_injective (AdjoinRoot.of p).injective).eq_pow_of_pow_eq_one h
  exact hof (residue 𝔹 z ^ i) (by rw [map_pow, hi])

end Arithmetic

/-- The residue, value and Henselian arithmetic of the actual separable inertia fixed field. -/
theorem separableUnramifiedArithmetic : SeparableUnramifiedArithmeticStatement.{u} := by
  intro F _ _ _ _
  have hv := fixedFieldValuesFromBase F
  exact ⟨fixedFieldResidueIsAlgClosure F, hv, fixedFieldIntrinsicDiscrete_of_valuesFromBase F hv,
    fixedFieldIntegersIsDVR_of_valuesFromBase F hv, fixedFieldIntegersIsHenselian F⟩

end Langlands.LocalGalois.Separable
