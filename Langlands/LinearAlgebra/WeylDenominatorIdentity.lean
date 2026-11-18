import Langlands.LinearAlgebra.SimpleReflectionWords
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Support

/-! # Alternating elements of `ℤ[M]` and the Weyl denominator identity -/

noncomputable section

open Set Function AddMonoidAlgebra

namespace Langlands.LinearAlgebra.WeylCharacter

open DominantTriangular

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {P : RootPairing ι ℤ M N}

/-! ### The action of linear automorphisms on `ℤ[M]` -/

/-- The ring automorphism of `ℤ[M]` induced by a linear automorphism of `M`. -/
def act (w : M ≃ₗ[ℤ] M) : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ w.toAddEquiv

@[simp]
theorem act_single (w : M ≃ₗ[ℤ] M) (μ : M) (r : ℤ) : act w (single μ r) = single (w μ) r := by
  simp [act]

theorem coeff_act (w : M ≃ₗ[ℤ] M) (f : AddMonoidAlgebra ℤ M) (μ : M) :
    (act w f).coeff μ = f.coeff (w.symm μ) := by
  simp [act, Finsupp.equivMapDomain_apply]

theorem act_mul (v w : M ≃ₗ[ℤ] M) (f : AddMonoidAlgebra ℤ M) :
    act (v * w) f = act v (act w f) := by
  ext μ
  simp only [coeff_act]
  rfl

theorem act_one (f : AddMonoidAlgebra ℤ M) : act (1 : M ≃ₗ[ℤ] M) f = f := by
  ext μ
  simp only [coeff_act]
  rfl

/-! ### Alternating elements -/

variable (P) in
/-- An element `f` of `ℤ[M]` is alternating when `w f = det(w) f` for every `w` in the
reflection group. -/
def IsAlternating (f : AddMonoidAlgebra ℤ M) : Prop :=
  ∀ w ∈ reflectionGroup P, act w f = LinearMap.det (w : M ≃ₗ[ℤ] M).toLinearMap • f

theorem IsAlternating.sub {f g : AddMonoidAlgebra ℤ M} (hf : IsAlternating P f)
    (hg : IsAlternating P g) : IsAlternating P (f - g) := fun w hw => by
  rw [map_sub, hf w hw, hg w hw, smul_sub]

theorem det_mul_self_eq_one (w : M ≃ₗ[ℤ] M) :
    LinearMap.det w.toLinearMap * LinearMap.det w.toLinearMap = 1 := by
  rw [← LinearEquiv.coe_det, ← Units.val_mul, Int.units_mul_self, Units.val_one]

theorem IsAlternating.coeff_apply {f : AddMonoidAlgebra ℤ M} (hf : IsAlternating P f)
    {w : M ≃ₗ[ℤ] M} (hw : w ∈ reflectionGroup P) (μ : M) :
    f.coeff μ = LinearMap.det w.toLinearMap * f.coeff (w μ) := by
  have h := congrArg (fun g : AddMonoidAlgebra ℤ M => g.coeff (w μ)) (hf w hw)
  simp only [coeff_act, LinearEquiv.symm_apply_apply, coeff_smul, Finsupp.smul_apply,
    smul_eq_mul] at h
  exact h

section Simple

variable (b : P.Base) [Finite ι] [P.IsReduced] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- It suffices to check alternation on the simple reflections. -/
theorem isAlternating_of_simple {f : AddMonoidAlgebra ℤ M}
    (h : ∀ a : b.support, act (P.reflection a) f = -f) : IsAlternating P f := by
  intro w hw
  obtain ⟨L, rfl⟩ := exists_word_eq b hw
  rw [det_word]
  induction L with
  | nil => simp [act_one]
  | cons a L ih =>
    rw [word_cons, act_mul, ih (word_mem b L), map_zsmul, h, List.length_cons, pow_succ,
      smul_neg, mul_neg, mul_one, neg_smul]

end Simple

/-! ### Alternating sums over the reflection group -/

variable (P) in
/-- The alternating sum `J(ν) = ∑_{w ∈ W} det(w) e^{w ν}`. -/
def alternant (ν : M) : AddMonoidAlgebra ℤ M :=
  ∑ᶠ w : reflectionGroup P,
    single ((w : M ≃ₗ[ℤ] M) ν) (LinearMap.det (w : M ≃ₗ[ℤ] M).toLinearMap)

theorem alternant_eq_sum [Fintype (reflectionGroup P)] (ν : M) :
    alternant P ν = ∑ w : reflectionGroup P,
      single ((w : M ≃ₗ[ℤ] M) ν) (LinearMap.det (w : M ≃ₗ[ℤ] M).toLinearMap) :=
  finsum_eq_sum_of_fintype _

theorem isAlternating_alternant [Finite ι] (ν : M) : IsAlternating P (alternant P ν) := by
  classical
  intro v hv
  let _ : Fintype (reflectionGroup P) := Fintype.ofFinite _
  let v' : reflectionGroup P := ⟨v, hv⟩
  rw [alternant_eq_sum, map_sum, Finset.smul_sum]
  simp only [act_single]
  refine Fintype.sum_equiv (Equiv.mulLeft v') _ _ fun w => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, LinearEquiv.mul_apply, smul_single,
    smul_eq_mul, v']
  rw [det_mul, ← mul_assoc, det_mul_self_eq_one, one_mul]

theorem det_one : LinearMap.det (1 : M ≃ₗ[ℤ] M).toLinearMap = 1 := by
  rw [← LinearEquiv.coe_det, map_one, Units.val_one]

/-! ### Coefficients at strictly dominant elements and uniqueness -/

section Dominant

variable (b : P.Base) [Finite ι] [P.IsReduced]

open Classical in
/-- The coefficient of `J(ν₀)` at a dominant `ν`, for strictly dominant `ν₀`. -/
theorem coeff_alternant_of_isStrictlyDominant {ν₀ ν : M} (hν₀ : IsStrictlyDominant b ν₀)
    (hν : IsDominant P b ν) : (alternant P ν₀).coeff ν = if ν₀ = ν then 1 else 0 := by
  classical
  let _ : Fintype (reflectionGroup P) := Fintype.ofFinite _
  rw [alternant_eq_sum, coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single (1 : reflectionGroup P)]
  · simp only [coeff_single, Finsupp.single_apply, OneMemClass.coe_one, LinearEquiv.coe_one,
      id_eq, det_one]
  · intro w _ hw
    rw [coeff_single, Finsupp.single_apply, ite_eq_right_iff]
    intro hwν
    exact absurd (Subtype.ext (eq_one_of_isDominant_apply b w.2 hν₀ (hwν ▸ hν))) hw
  · intro h
    exact absurd (Finset.mem_univ _) h

variable [Module.Free ℤ M] [Module.Finite ℤ M]

omit [P.IsReduced] in
/-- An alternating element vanishing at every strictly dominant element is zero. -/
theorem eq_zero_of_isAlternating {f : AddMonoidAlgebra ℤ M} (hf : IsAlternating P f)
    (h : ∀ ν, IsStrictlyDominant b ν → f.coeff ν = 0) : f = 0 := by
  ext μ
  rw [coeff_zero, Finsupp.zero_apply]
  obtain ⟨ν, hνmem, hν⟩ := exists_dominant_mem_orbit (b := b) μ
  obtain ⟨w, hw, rfl⟩ := mem_orbit_iff.mp hνmem
  rw [hf.coeff_apply hw μ]
  suffices H : f.coeff (w μ) = 0 by rw [H, mul_zero]
  by_cases hs : IsStrictlyDominant b (w μ)
  · exact h _ hs
  · simp only [IsStrictlyDominant, not_forall, not_lt] at hs
    obtain ⟨a, ha⟩ := hs
    have h0 : P.coroot' a (w μ) = 0 := le_antisymm ha (hν a)
    have hfix : P.reflection a (w μ) = w μ := by
      rw [RootPairing.reflection_apply, h0, zero_smul, sub_zero]
    have := hf.coeff_apply (reflection_mem_reflectionGroup P a) (w μ)
    rw [hfix, det_reflection] at this
    omega

open Classical in
/-- An alternating element whose coefficients at strictly dominant elements are those of
`J(ν₀)` equals `J(ν₀)`. -/
theorem eq_alternant {f : AddMonoidAlgebra ℤ M} {ν₀ : M} (hf : IsAlternating P f)
    (hν₀ : IsStrictlyDominant b ν₀)
    (h : ∀ ν, IsStrictlyDominant b ν → f.coeff ν = if ν₀ = ν then 1 else 0) :
    f = alternant P ν₀ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_isAlternating b (hf.sub (isAlternating_alternant ν₀)) fun ν hν => ?_
  rw [coeff_sub, Finsupp.sub_apply, h ν hν,
    coeff_alternant_of_isStrictlyDominant b hν₀ hν.isDominant, sub_self]

end Dominant

/-! ### Elements supported below a given element -/

variable (b : P.Base) in
/-- `f` is supported below `ν₀`: every `μ` with a nonzero coefficient has `ν₀ - μ` in the
positive cone. -/
def IsBelow (f : AddMonoidAlgebra ℤ M) (ν₀ : M) : Prop :=
  ∀ μ, f.coeff μ ≠ 0 → ν₀ - μ ∈ positiveCone P b

section Below

variable {b : P.Base}

theorem IsBelow.mul {f g : AddMonoidAlgebra ℤ M} {ν₀ ν₁ : M} (hf : IsBelow b f ν₀)
    (hg : IsBelow b g ν₁) : IsBelow b (f * g) (ν₀ + ν₁) := by
  classical
  intro μ hμ
  obtain ⟨x, hx, y, hy, rfl⟩ :=
    Finset.mem_add.mp (support_coeff_mul_subset f g (Finsupp.mem_support_iff.mpr hμ))
  have := add_mem (hf x (Finsupp.mem_support_iff.mp hx)) (hg y (Finsupp.mem_support_iff.mp hy))
  convert this using 1
  abel

theorem IsBelow.coeff_mul {f g : AddMonoidAlgebra ℤ M} {ν₀ ν₁ : M} (hf : IsBelow b f ν₀)
    (hg : IsBelow b g ν₁) : (f * g).coeff (ν₀ + ν₁) = f.coeff ν₀ * g.coeff ν₁ := by
  refine coeff_mul_add_of_uniqueAdd fun x y hx hy hxy => ?_
  have h1 := hf x (Finsupp.mem_support_iff.mp hx)
  have h2 := hg y (Finsupp.mem_support_iff.mp hy)
  have h3 : -(ν₀ - x) = ν₁ - y := by
    rw [neg_sub, sub_eq_sub_iff_add_eq_add, hxy, add_comm]
  have h4 := eq_zero_of_mem_positiveCone_of_neg_mem P b h1 (h3 ▸ h2)
  rw [h4, neg_zero, eq_comm, sub_eq_zero] at h3
  exact ⟨(sub_eq_zero.mp h4).symm, h3.symm⟩

theorem isBelow_single (μ : M) (r : ℤ) : IsBelow b (single μ r) μ := by
  classical
  intro ν hν
  rw [coeff_single, Finsupp.single_apply] at hν
  rw [show μ = ν from by_contra fun h => hν (ite_eq_right h), sub_self]
  exact zero_mem _

theorem isBelow_one_sub {α : M} (hα : α ∈ positiveCone P b) :
    IsBelow b (1 - single (-α) 1) 0 := by
  classical
  intro ν hν
  rw [one_def, coeff_sub, Finsupp.sub_apply, coeff_single, coeff_single, Finsupp.single_apply,
    Finsupp.single_apply] at hν
  by_cases h0 : (0 : M) = ν
  · rw [← h0, sub_self]
    exact zero_mem _
  · by_cases h1 : -α = ν
    · rwa [← h1, zero_sub, neg_neg]
    · simp [h0, h1] at hν

theorem coeff_one_sub_zero {α : M} (hα : α ≠ 0) : (1 - single (-α) 1 : AddMonoidAlgebra ℤ M).coeff 0 = 1 := by
  classical
  rw [one_def, coeff_sub, Finsupp.sub_apply, coeff_single, coeff_single, Finsupp.single_apply,
    Finsupp.single_apply, ite_eq_left rfl, ite_eq_right (neg_ne_zero.mpr hα)]
  rfl

theorem isBelow_prod {κ : Type*} (s : Finset κ) (g : κ → AddMonoidAlgebra ℤ M)
    (h : ∀ i ∈ s, IsBelow b (g i) 0) :
    IsBelow b (∏ i ∈ s, g i) 0 ∧ (∏ i ∈ s, g i).coeff 0 = ∏ i ∈ s, (g i).coeff 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · rw [Finset.prod_empty, one_def]
      exact isBelow_single 0 1
    · rw [Finset.prod_empty, Finset.prod_empty, one_def, coeff_single, Finsupp.single_eq_same]
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha' := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have := ha'.mul ih1
    rw [add_zero] at this
    refine ⟨this, ?_⟩
    have h' := ha'.coeff_mul ih1
    rw [add_zero] at h'
    rw [h', ih2]

end Below

/-! ### The Weyl denominator -/

section Denominator

variable (b : P.Base) [Fintype ι]

open Classical in
/-- The indices of the positive roots. -/
def posRoots : Finset ι :=
  Finset.univ.filter fun i => P.root i ∈ positiveCone P b

theorem mem_posRoots {i : ι} : i ∈ posRoots b ↔ P.root i ∈ positiveCone P b := by
  simp [posRoots]

/-- The Weyl denominator `e^ρ ∏_{α > 0} (1 - e^{-α})`. -/
def denominator (ρ : M) : AddMonoidAlgebra ℤ M :=
  single ρ 1 * ∏ i ∈ posRoots b, (1 - single (-P.root i) 1)

theorem isBelow_denominator (ρ : M) :
    IsBelow b (denominator b ρ) ρ ∧ (denominator b ρ).coeff ρ = 1 := by
  obtain ⟨h1, h2⟩ := isBelow_prod (b := b) (posRoots b)
    (fun i => (1 - single (-P.root i) 1 : AddMonoidAlgebra ℤ M))
    fun i hi => isBelow_one_sub ((mem_posRoots b).mp hi)
  have hb := (isBelow_single (b := b) ρ 1).mul h1
  have hc := (isBelow_single (b := b) ρ 1).coeff_mul h1
  rw [add_zero] at hb hc
  refine ⟨hb, ?_⟩
  rw [denominator, hc, h2, Finset.prod_eq_one fun i _ => coeff_one_sub_zero (P.ne_zero i),
    coeff_single, Finsupp.single_eq_same, mul_one]

variable [P.IsReduced]

theorem act_reflection_denominator {ρ : M}
    (hρ : 2 • ρ = ∑ᶠ (i : ι) (_ : P.root i ∈ positiveCone P b), P.root i) (a : b.support) :
    act (P.reflection a) (denominator b ρ) = -denominator b ρ := by
  classical
  have hact : ∀ i, act (P.reflection a) (1 - single (-P.root i) 1) =
      1 - single (-P.root (P.reflectionPerm a i)) 1 := by
    intro i
    simp only [map_sub, map_one, act_single, map_neg, RootPairing.root_reflectionPerm]
  have hρ' : P.reflection a ρ = ρ - P.root a := by
    rw [RootPairing.reflection_apply]
    have : P.coroot' a ρ = 1 := pairing_rho_eq_one b hρ a
    rw [this, one_smul]
  have ha : (a : ι) ∈ posRoots b := (mem_posRoots b).mpr (root_mem_positiveCone P b a)
  have hπa : P.reflectionPerm a a ∉ posRoots b := by
    rw [mem_posRoots]
    exact root_reflectionPerm_self_notMem b a.2
  have hmaps : ∀ i ∈ (posRoots b).erase a, P.reflectionPerm a i ∈ (posRoots b).erase a := by
    intro i hi
    rw [Finset.mem_erase] at hi ⊢
    have hia' : i ≠ P.reflectionPerm a a := fun h => hπa (h ▸ hi.2)
    refine ⟨fun h => hia' ?_, ?_⟩
    · have h' := congrArg (P.reflectionPerm a) h
      rwa [RootPairing.reflectionPerm_self] at h'
    · rw [mem_posRoots, root_reflectionPerm_mem_iff b a.2 hi.1 hia']
      exact (mem_posRoots b).mp hi.2
  have herase : ∏ i ∈ (posRoots b).erase a,
      (1 - single (-P.root (P.reflectionPerm a i)) 1 : AddMonoidAlgebra ℤ M) =
      ∏ i ∈ (posRoots b).erase a, (1 - single (-P.root i) 1) :=
    Finset.prod_nbij' (P.reflectionPerm a) (P.reflectionPerm a) hmaps hmaps
      (fun i _ => P.reflectionPerm_self _ _) (fun i _ => P.reflectionPerm_self _ _)
      fun i _ => rfl
  have e1 := Finset.mul_prod_erase (posRoots b)
    (fun i => (1 - single (-P.root (P.reflectionPerm a i)) 1 : AddMonoidAlgebra ℤ M)) ha
  have e2 := Finset.mul_prod_erase (posRoots b)
    (fun i => (1 - single (-P.root i) 1 : AddMonoidAlgebra ℤ M)) ha
  have hπroot : -P.root (P.reflectionPerm a a) = P.root a := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, neg_neg]
  have key : single (ρ - P.root a) 1 * (1 - single (P.root a) 1) =
      -(single ρ 1 * (1 - single (-P.root a) 1) : AddMonoidAlgebra ℤ M) := by
    simp only [mul_sub, mul_one, single_mul_single, sub_add_cancel, neg_sub, ← sub_eq_add_neg]
  rw [denominator, map_mul, act_single, map_prod, hρ']
  simp only [hact]
  rw [← e1, ← e2, herase, hπroot, ← mul_assoc, key, neg_mul, mul_assoc]

theorem isStrictlyDominant_rho {ρ : M}
    (hρ : 2 • ρ = ∑ᶠ (i : ι) (_ : P.root i ∈ positiveCone P b), P.root i) :
    IsStrictlyDominant b ρ := fun a => by
  rw [pairing_rho_eq_one b hρ a]
  exact one_pos

/-- A strictly dominant element below `ρ` equals `ρ`. -/
theorem eq_rho_of_isStrictlyDominant {ρ ν : M}
    (hρ : 2 • ρ = ∑ᶠ (i : ι) (_ : P.root i ∈ positiveCone P b), P.root i)
    (hν : IsStrictlyDominant b ν) (hle : ρ - ν ∈ positiveCone P b) : ν = ρ := by
  have hdom : IsDominant P b (ν - ρ) := fun a => by
    have h1 := hν a
    have h2 := pairing_rho_eq_one b hρ a
    rw [map_sub, LinearMap.sub_apply, h2]
    omega
  by_contra hne
  have hd0 : ρ - ν ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h1 := rootForm_nonneg_of_mem_positiveCone hdom hle
  have h2 := rootForm_self_pos_of_mem_positiveCone hle hd0
  rw [show ν - ρ = -(ρ - ν) by abel, map_neg] at h1
  linarith

variable [Module.Free ℤ M] [Module.Finite ℤ M]

theorem isAlternating_denominator {ρ : M}
    (hρ : 2 • ρ = ∑ᶠ (i : ι) (_ : P.root i ∈ positiveCone P b), P.root i) :
    IsAlternating P (denominator b ρ) :=
  isAlternating_of_simple b (act_reflection_denominator b hρ)

/-- An alternating element supported below a strictly dominant `ν₀`, with coefficient `1` at
`ν₀`, and with no other strictly dominant element in its support, equals `J(ν₀)`. -/
theorem eq_alternant_of_isBelow {f : AddMonoidAlgebra ℤ M} {ν₀ : M} (hf : IsAlternating P f)
    (hν₀ : IsStrictlyDominant b ν₀) (h1 : f.coeff ν₀ = 1)
    (h : ∀ ν, IsStrictlyDominant b ν → f.coeff ν ≠ 0 → ν = ν₀) :
    f = alternant P ν₀ := by
  refine eq_alternant b hf hν₀ fun ν hν => ?_
  by_cases hνν : ν₀ = ν
  · rw [ite_eq_left hνν, ← hνν, h1]
  · rw [ite_eq_right hνν]
    by_contra hne
    exact hνν (h ν hν hne).symm

/-- **Weyl denominator identity.** `e^ρ ∏_{α > 0} (1 - e^{-α}) = ∑_{w ∈ W} det(w) e^{w ρ}`. -/
theorem denominator_eq_alternant {ρ : M}
    (hρ : 2 • ρ = ∑ᶠ (i : ι) (_ : P.root i ∈ positiveCone P b), P.root i) :
    denominator b ρ = alternant P ρ :=
  eq_alternant_of_isBelow b (isAlternating_denominator b hρ) (isStrictlyDominant_rho b hρ)
    (isBelow_denominator b ρ).2 fun ν hν hne =>
      eq_rho_of_isStrictlyDominant b hρ hν ((isBelow_denominator b ρ).1 ν hne)

end Denominator

end Langlands.LinearAlgebra.WeylCharacter
