import Langlands.Galois.Local.SeparableUnramifiedArithmeticStatement
import Mathlib.RingTheory.Polynomial.GaussLemma

noncomputable section

open Polynomial IsLocalRing ValuativeRel
open scoped NNReal

namespace Langlands.LocalGalois.Separable

/-- Valuation rings of separably closed fields are Henselian: induction on the degree. -/
theorem sepClosed_hensel_aux {K : Type*} [Field K] [IsSepClosed K] (O : ValuationSubring K)
    (n : ℕ) : ∀ f : O[X], f.natDegree = n → f.Monic → ∀ a₀ : O,
      f.eval a₀ ∈ maximalIdeal O → IsUnit (f.derivative.eval a₀) →
        ∃ a : O, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal O := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn hf a₀ hroot hder₀
  have hd : derivative f ≠ 0 := by
    intro h
    rw [h, eval_zero] at hder₀
    exact not_isUnit_zero hder₀
  by_cases hirr : Irreducible f
  · have hirr' : Irreducible (f.map (algebraMap O K)) :=
      (hf.irreducible_iff_irreducible_map_fraction_map).mp hirr
    have hsep : (f.map (algebraMap O K)).Separable := by
      rw [separable_iff_derivative_ne_zero hirr', derivative_map]
      exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective O K)).mpr hd
    have hdeg := IsSepClosed.degree_eq_one_of_irreducible K hirr' hsep
    rw [degree_map_eq_of_injective (IsFractionRing.injective O K)] at hdeg
    have hnat : f.natDegree = 1 := natDegree_eq_of_degree_eq_some hdeg
    obtain ⟨c, rfl⟩ : ∃ c, f = X + C c := ⟨_, hf.eq_X_add_C hnat⟩
    refine ⟨-c, by simp [IsRoot], ?_⟩
    have h : -c - a₀ = -(eval a₀ (X + C c)) := by simp; ring
    rw [h]
    exact (maximalIdeal O).neg_mem hroot
  · have hnu : ¬IsUnit f := by
      intro hu
      exact hd (derivative_of_natDegree_zero (natDegree_eq_zero_of_isUnit hu))
    have hfac : ¬∀ a b : O[X], f = a * b → IsUnit a ∨ IsUnit b :=
      fun H => hirr (irreducible_iff.mpr ⟨hnu, H⟩)
    push Not at hfac
    obtain ⟨g, h, hgh, hg, hh⟩ := hfac
    have hlc : g.leadingCoeff * h.leadingCoeff = 1 := by
      rw [← leadingCoeff_mul, ← hgh, hf.leadingCoeff]
    obtain ⟨g₁, hg₁def⟩ : ∃ p, p = g * C h.leadingCoeff := ⟨_, rfl⟩
    obtain ⟨k₁, hk₁def⟩ : ∃ p, p = h * C g.leadingCoeff := ⟨_, rfl⟩
    have hf₁ : f = g₁ * k₁ := by
      rw [hgh, hg₁def, hk₁def]
      calc g * h = g * h * C (g.leadingCoeff * h.leadingCoeff) := by rw [hlc, C_1, mul_one]
        _ = g * C h.leadingCoeff * (h * C g.leadingCoeff) := by rw [C_mul]; ring
    have hg₁m : g₁.Monic := by
      rw [Monic, hg₁def, leadingCoeff_mul, leadingCoeff_C, hlc]
    have hk₁m : k₁.Monic := by
      rw [Monic, hk₁def, leadingCoeff_mul, leadingCoeff_C, mul_comm, hlc]
    have hg₁u : ¬IsUnit g₁ := by
      intro hu
      apply hg
      have : g = g₁ * C g.leadingCoeff := by
        rw [hg₁def, mul_assoc, ← C_mul, mul_comm h.leadingCoeff, hlc, C_1, mul_one]
      rw [this]
      exact hu.mul (isUnit_C.mpr (IsUnit.of_mul_eq_one _ hlc))
    have hk₁u : ¬IsUnit k₁ := by
      intro hu
      apply hh
      have : h = k₁ * C h.leadingCoeff := by
        rw [hk₁def, mul_assoc, ← C_mul, hlc, C_1, mul_one]
      rw [this]
      exact hu.mul (isUnit_C.mpr (IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hlc)))
    have hg₁d : g₁.natDegree ≠ 0 := fun h0 =>
      hg₁u (hg₁m.natDegree_eq_zero.mp h0 ▸ isUnit_one)
    have hk₁d : k₁.natDegree ≠ 0 := fun h0 =>
      hk₁u (hk₁m.natDegree_eq_zero.mp h0 ▸ isUnit_one)
    have hdegsum : f.natDegree = g₁.natDegree + k₁.natDegree := by
      rw [hf₁, hg₁m.natDegree_mul hk₁m]
    have hev : f.eval a₀ = g₁.eval a₀ * k₁.eval a₀ := by rw [hf₁, eval_mul]
    have hder : f.derivative.eval a₀ =
        g₁.derivative.eval a₀ * k₁.eval a₀ + g₁.eval a₀ * k₁.derivative.eval a₀ := by
      rw [hf₁, derivative_mul, eval_add, eval_mul, eval_mul]
    rw [hev] at hroot
    rcases (Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal O)).mem_or_mem hroot with
      hg₁a | hk₁a
    · have hunit : IsUnit (g₁.derivative.eval a₀) := by
        by_contra hnu'
        have hm : g₁.derivative.eval a₀ ∈ maximalIdeal O := hnu'
        have hmem : f.derivative.eval a₀ ∈ maximalIdeal O := by
          rw [hder]
          exact (maximalIdeal O).add_mem ((maximalIdeal O).mul_mem_right (k₁.eval a₀) hm)
            ((maximalIdeal O).mul_mem_right (k₁.derivative.eval a₀) hg₁a)
        exact hmem hder₀
      obtain ⟨a, ha, hsub⟩ := ih g₁.natDegree (by omega) g₁ rfl hg₁m a₀ hg₁a hunit
      refine ⟨a, ?_, hsub⟩
      rw [IsRoot, hf₁, eval_mul, ha.eq_zero, zero_mul]
    · have hunit : IsUnit (k₁.derivative.eval a₀) := by
        by_contra hnu'
        have hm : k₁.derivative.eval a₀ ∈ maximalIdeal O := hnu'
        have hmem : f.derivative.eval a₀ ∈ maximalIdeal O := by
          rw [hder]
          exact (maximalIdeal O).add_mem
            ((maximalIdeal O).mul_mem_left (g₁.derivative.eval a₀) hk₁a)
            ((maximalIdeal O).mul_mem_left (g₁.eval a₀) hm)
        exact hmem hder₀
      obtain ⟨a, ha, hsub⟩ := ih k₁.natDegree (by omega) k₁ rfl hk₁m a₀ hk₁a hunit
      refine ⟨a, ?_, hsub⟩
      rw [IsRoot, hf₁, eval_mul, ha.eq_zero, mul_zero]

/-- The valuation ring of a separably closed field is Henselian. -/
theorem sepClosed_henselian {K : Type*} [Field K] [IsSepClosed K] (O : ValuationSubring K) :
    HenselianLocalRing O where
  is_henselian f hf a₀ h₁ h₂ := sepClosed_hensel_aux O _ f rfl hf a₀ h₁ h₂

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance henselianNormedField : NontriviallyNormedField F := localNormedField F
local instance henselianUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance henselianComplete : CompleteSpace F := localNormedField_complete F

/-- The actual integer ring of the separable inertia fixed field is Henselian. -/
theorem fixedFieldIntegersIsHenselian : FixedFieldIntegersIsHenselian F := by
  let A := sepClosureIntegers F
  let B := fixedFieldIntegers F
  let i : B →+* A := fixedFieldIntegerInclusion F
  let : HenselianLocalRing A := sepClosed_henselian (sepClosureIntegers F)
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A => (z : SeparableClosure F)) h
  refine { is_henselian := ?_ }
  intro f hf a₀ hroot hder
  let g := f.map i
  have hroot' : g.eval (i a₀) ∈ maximalIdeal A := by
    rw [eval_map_apply]
    exact map_nonunit i _ hroot
  have hder' : IsUnit (g.derivative.eval (i a₀)) := by
    rw [derivative_map, eval_map_apply]
    exact hder.map i
  obtain ⟨a, ha, hsub⟩ := HenselianLocalRing.is_henselian g (hf.map i) (i a₀) hroot' hder'
  have hres : residue A a = residue A (i a₀) := by
    rwa [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hsub
  have hdera : IsUnit (g.derivative.eval a) := by
    apply isUnit_of_map_unit (residue A)
    rw [← eval_map_apply, hres, eval_map_apply]
    exact hder'.map (residue A)
  have hfix : (a : SeparableClosure F) ∈ inertiaFixedField F := by
    rw [mem_inertiaFixedField_iff]
    intro σ hσ
    let e : A →+* A := (integerAut F (SeparableClosure F) σ).toRingHom
    have he : e.comp i = i := by
      apply RingHom.ext
      intro x
      apply Subtype.ext
      change σ ((x : inertiaFixedField F) : SeparableClosure F) = _
      exact (mem_inertiaFixedField_iff F _).mp (x : inertiaFixedField F).property σ hσ
    have hg : g.map e = g := by
      change (f.map i).map e = f.map i
      rw [Polynomial.map_map, he]
    have hea : g.eval (e a) = 0 := by
      rw [← hg, eval_map_apply, ha.eq_zero, map_zero]
    have hcong : a - e a ∈ maximalIdeal A := by
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact ((mem_separableInertia_iff F σ).mp hσ a).symm
    have hae : a = e a :=
      IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub ha.eq_zero hea hcong hdera
    exact (congrArg (fun z : A => (z : SeparableClosure F)) hae).symm
  let b : B := ⟨⟨(a : SeparableClosure F), hfix⟩, a.property⟩
  have hb : i b = a := rfl
  refine ⟨b, ?_, ?_⟩
  · apply hi
    rw [map_zero, ← eval_map_apply, hb]
    exact ha.eq_zero
  · intro hu
    apply hsub
    rw [← hb, ← map_sub]
    exact hu.map i

/-- A chosen simple Hensel lift in the actual fixed-field integer ring,
with the root equation and residue-class condition included in its type. -/
def fixedFieldHenselRoot (f : (fixedFieldIntegers F)[X]) (hf : f.Monic)
    (a₀ : fixedFieldIntegers F) (hroot : f.eval a₀ ∈ maximalIdeal (fixedFieldIntegers F))
    (hder : IsUnit (f.derivative.eval a₀)) :
    {a : fixedFieldIntegers F // f.IsRoot a ∧ a - a₀ ∈ maximalIdeal (fixedFieldIntegers F)} := by
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  exact ⟨Classical.choose (HenselianLocalRing.is_henselian f hf a₀ hroot hder),
    Classical.choose_spec (HenselianLocalRing.is_henselian f hf a₀ hroot hder)⟩

end Langlands.LocalGalois.Separable
