import Langlands.Representation.Whittaker.PrerequisiteInterfaces
import Mathlib.Algebra.BigOperators.Fin

/-! # The all-ranks entrywise Whittaker character -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis
open scoped BigOperators

universe uF uV

variable {F : Type uF} [CommRing F]

/-- The actual upper-unipotent character, including rank zero, for a raw additive character. -/
def entrywiseCharacter (ψ : AddChar F ℂ) : (d : ℕ) → upperUnipotent d F →* ℂˣ
  | 0 => 1
  | _n + 1 => ψ.toMonoidHom.toHomUnits.comp UpperUnipotent.superdiagonalSum

/-- For positive rank the character evaluates on the sum of adjacent entries. -/
@[simp] theorem entrywiseCharacter_apply_sum (ψ : AddChar F ℂ) (n : ℕ)
    (g : upperUnipotent (n + 1) F) :
    (entrywiseCharacter ψ (n + 1) g : ℂ) =
      ψ (∑ i : Fin n, g.val.val i.castSucc i.succ) := rfl

private theorem addChar_finset_sum {ι : Type*} (ψ : AddChar F ℂ)
    (s : Finset ι) (f : ι → F) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]

/-- The double-index product is the usual product over adjacent entries. -/
theorem entrywiseProduct_eq_adjacentProduct (ψ : AddChar F ℂ) (n : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (∏ a : Fin (n + 1), ∏ b : Fin (n + 1),
      if b.val = a.val + 1 then ψ (g.val a b) else 1) =
      ∏ i : Fin n, ψ (g.val i.castSucc i.succ) := by
  classical
  rw [Fin.prod_univ_castSucc]
  have hlast : (∏ b : Fin (n + 1),
      if b.val = (Fin.last n).val + 1 then ψ (g.val (Fin.last n) b) else 1) = 1 := by
    apply Finset.prod_eq_one
    intro b _
    rw [ite_eq_right]
    simp only [Fin.val_last]
    omega
  rw [hlast, mul_one]
  apply Finset.prod_congr rfl
  intro a _
  rw [Finset.prod_eq_single a.succ]
  · simp
  · intro b _ hba
    apply ite_eq_right
    intro he
    apply hba
    apply Fin.ext
    exact he
  · simp

/-- Evaluation is exactly the product occurring in `InducedWhittakerTypeStatement`. -/
theorem entrywiseCharacter_apply (ψ : AddChar F ℂ) (d : ℕ)
    (g : upperUnipotent d F) :
    (entrywiseCharacter ψ d g : ℂ) =
      ∏ a : Fin d, ∏ b : Fin d,
        if b.val = a.val + 1 then ψ (g.val.val a b) else 1 := by
  cases d with
  | zero => simp [entrywiseCharacter]
  | succ n =>
    rw [entrywiseProduct_eq_adjacentProduct, entrywiseCharacter_apply_sum]
    exact addChar_finset_sum ψ Finset.univ _

@[simp] theorem entrywiseCharacter_rankZero (ψ : AddChar F ℂ) :
    entrywiseCharacter ψ 0 = 1 := rfl

@[simp] theorem entrywiseCharacter_rankOne (ψ : AddChar F ℂ) :
    entrywiseCharacter ψ 1 = 1 := by
  ext g
  simp

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Functional membership is the exact inline condition of the induced-type target. -/
theorem mem_functionals_entrywiseCharacter_iff (ψ : AddChar F ℂ) (d : ℕ)
    (ρ : Representation ℂ (Langlands.GeneralLinear d F) V) (ℓ : Module.Dual ℂ V) :
    ℓ ∈ functionals (upperUnipotent d F) (entrywiseCharacter ψ d) ρ ↔
      ∀ g : Langlands.GeneralLinear d F,
        ((∀ a b, b < a → g.val a b = 0) ∧ ∀ a, g.val a a = 1) →
        ∀ v, ℓ (ρ g v) =
          (∏ a : Fin d, ∏ b : Fin d,
            if b.val = a.val + 1 then ψ (g.val a b) else 1) * ℓ v := by
  constructor
  · intro h g hg v
    let u : upperUnipotent d F := ⟨g, ⟨fun _ _ hab => hg.1 _ _ hab, hg.2⟩⟩
    simpa only [entrywiseCharacter_apply] using h u v
  · intro h u v
    rw [entrywiseCharacter_apply]
    exact h u.val ⟨fun _ _ hab => UpperUnipotent.entry_eq_zero u hab,
      UpperUnipotent.entry_diag u⟩ v

/-- Agreement with the published positive-rank single-product covariance predicate. -/
theorem mem_functionals_entrywiseCharacter_iff_entrywise (ψ : AddChar F ℂ) (n : ℕ)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) (ℓ : Module.Dual ℂ V) :
    ℓ ∈ functionals (upperUnipotent (n + 1) F) (entrywiseCharacter ψ (n + 1)) ρ ↔
      EntrywiseEquivariant ρ ψ ℓ := by
  rw [mem_functionals_entrywiseCharacter_iff]
  simp only [entrywiseProduct_eq_adjacentProduct, EntrywiseEquivariant, and_imp]

section Unitary

variable [TopologicalSpace F]

/-- Agreement with the published standard character, as units-valued homomorphisms. -/
theorem entrywiseCharacter_eq_standardCharacter (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    entrywiseCharacter ψ.complex (n + 1) = standardCharacter ψ n := by
  ext g
  rfl

/-- The published raw-character packaging identifies the all-ranks construction at positive rank. -/
theorem entrywiseCharacter_eq_standardCharacter_ofComplex (ψ : AddChar F ℂ)
    (hc : Continuous ψ) (hne : ψ ≠ 1) (hu : ∀ x, ‖ψ x‖ = 1) (n : ℕ) :
    entrywiseCharacter ψ (n + 1) =
      standardCharacter (UnitaryAdditiveCharacter.ofComplex ψ hc hne hu) n :=
  entrywiseCharacter_eq_standardCharacter (UnitaryAdditiveCharacter.ofComplex ψ hc hne hu) n

/-- Literal equality of the existing functional submodules for the packaged raw character. -/
theorem functionals_entrywiseCharacter_eq_glFunctionals (ψ : AddChar F ℂ)
    (hc : Continuous ψ) (hne : ψ ≠ 1) (hu : ∀ x, ‖ψ x‖ = 1) (n : ℕ)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    functionals (upperUnipotent (n + 1) F) (entrywiseCharacter ψ (n + 1)) ρ =
      glFunctionals (UnitaryAdditiveCharacter.ofComplex ψ hc hne hu) n ρ := by
  rw [entrywiseCharacter_eq_standardCharacter_ofComplex ψ hc hne hu]

/-- Existing `glFunctionals` consumers can use the target's double-index matrix condition. -/
theorem mem_glFunctionals_ofComplex_iff_doubleEntrywise (ψ : AddChar F ℂ)
    (hc : Continuous ψ) (hne : ψ ≠ 1) (hu : ∀ x, ‖ψ x‖ = 1) (n : ℕ)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) (ℓ : Module.Dual ℂ V) :
    ℓ ∈ glFunctionals (UnitaryAdditiveCharacter.ofComplex ψ hc hne hu) n ρ ↔
      ∀ g : Langlands.GeneralLinear (n + 1) F,
        ((∀ a b, b < a → g.val a b = 0) ∧ ∀ a, g.val a a = 1) →
        ∀ v, ℓ (ρ g v) =
          (∏ a : Fin (n + 1), ∏ b : Fin (n + 1),
            if b.val = a.val + 1 then ψ (g.val a b) else 1) * ℓ v := by
  rw [← functionals_entrywiseCharacter_eq_glFunctionals ψ hc hne hu]
  exact mem_functionals_entrywiseCharacter_iff ψ (n + 1) ρ ℓ

end Unitary
end Langlands.Whittaker
