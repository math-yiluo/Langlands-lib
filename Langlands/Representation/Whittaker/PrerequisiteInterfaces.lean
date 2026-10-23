import Langlands.Representation.Whittaker.PrerequisitesStatement
import Langlands.Representation.Whittaker.CharacterChange

/-! # Entrywise interfaces for Whittaker prerequisites -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter

universe uF

variable {F : Type uF} [AddGroup F] [TopologicalSpace F]

/-- Package a continuous nontrivial complex character of unit norm. -/
def ofComplex (ψ : AddChar F ℂ) (hc : Continuous ψ) (hne : ψ ≠ 1)
    (hu : ∀ x, ‖ψ x‖ = 1) : UnitaryAdditiveCharacter F where
  toAddChar :=
    { toFun := fun x => ⟨ψ x, mem_sphere_zero_iff_norm.mpr (hu x)⟩
      map_zero_eq_one' := Subtype.ext ψ.map_zero_eq_one
      map_add_eq_mul' := fun x y => Subtype.ext (ψ.map_add_eq_mul x y) }
  continuous_toFun := hc.subtype_mk _
  nontrivial := by
    intro h
    apply hne
    ext x
    exact congrArg (fun χ : AddChar F Circle => (χ x : ℂ)) h

@[simp] theorem ofComplex_complex (ψ : AddChar F ℂ) (hc : Continuous ψ) (hne : ψ ≠ 1)
    (hu : ∀ x, ‖ψ x‖ = 1) : (ofComplex ψ hc hne hu).complex = ψ := rfl

end Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter

namespace Langlands.Whittaker

open HarmonicAnalysis GeneralLinear
open scoped BigOperators

universe uF uV

variable {F : Type uF} [CommRing F] [TopologicalSpace F]
variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The entrywise covariance predicate appearing in the prerequisites target. -/
def EntrywiseEquivariant (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ψ : AddChar F ℂ) (ℓ : Module.Dual ℂ V) : Prop :=
  ∀ g : Langlands.GeneralLinear (n + 1) F,
    (∀ i j, j < i → g.val i j = 0) → (∀ i, g.val i i = 1) →
    ∀ v, ℓ (π g v) = (∏ i : Fin n, ψ (g.val i.castSucc i.succ)) * ℓ v

omit [TopologicalSpace F] in
private theorem addChar_sum {ι : Type*} (ψ : AddChar F ℂ) (s : Finset ι) (f : ι → F) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]

/-- The sum formula in the bundled character is the entrywise product formula. -/
theorem standardCharacter_eq_product (ψ : UnitaryAdditiveCharacter F)
    (g : upperUnipotent (n + 1) F) :
    (standardCharacter ψ n g : ℂ) =
      ∏ i : Fin n, ψ.complex (g.val.val i.castSucc i.succ) := by
  rw [standardCharacter_apply]
  exact addChar_sum ψ.complex Finset.univ _

/-- Membership in the published functional space is exactly entrywise covariance. -/
theorem mem_glFunctionals_iff_entrywise (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V) :
    ℓ ∈ glFunctionals ψ n π ↔ EntrywiseEquivariant π ψ.complex ℓ := by
  constructor
  · intro h g hlow hdiag v
    let u : upperUnipotent (n + 1) F := ⟨g, ⟨fun _ _ hij => hlow _ _ hij, hdiag⟩⟩
    simpa only [standardCharacter_eq_product] using h u v
  · intro h u v
    rw [standardCharacter_eq_product]
    exact h u.val (fun _ _ hij => UpperUnipotent.entry_eq_zero u hij)
      (UpperUnipotent.entry_diag u) v

/-- The entrywise orbit-function map is injective for a nonzero functional on
an irreducible representation. No admissibility or uniqueness is needed. -/
theorem entrywise_coefficient_injective (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    [Representation.IsIrreducible π] (ℓ : Module.Dual ℂ V) (hne : ℓ ≠ 0)
    (hℓ : EntrywiseEquivariant π ψ.complex ℓ) :
    Function.Injective (fun v => fun g => ℓ (π g v)) := by
  let L : glFunctionals ψ n π := ⟨ℓ, (mem_glFunctionals_iff_entrywise ψ π ℓ).mpr hℓ⟩
  intro v w h
  apply (modelEquiv π L hne).toLinearEquiv.injective
  apply Subtype.ext
  apply Subtype.ext
  exact h

section Field

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

@[simp] theorem scale_neg_one_complex (ψ : UnitaryAdditiveCharacter K) :
    (ψ.scale (-1)).complex = ψ.complex⁻¹ := by
  ext x
  change ψ.complex ((-1 : K) * x) = ψ.complex (-x)
  rw [neg_one_mul]

/-- Character translation preserves existence of a nonzero entrywise functional. -/
theorem entrywise_exists_scale_iff (ψ : UnitaryAdditiveCharacter K)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V) (a : Kˣ) :
    (∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ EntrywiseEquivariant π ψ.complex ℓ) ↔
    ∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ EntrywiseEquivariant π (ψ.scale a).complex ℓ := by
  let e := characterChangeFunctionalEquiv ψ π a
  constructor
  · rintro ⟨ℓ, hne, hℓ⟩
    let L : glFunctionals ψ n π := ⟨ℓ, (mem_glFunctionals_iff_entrywise ψ π ℓ).mpr hℓ⟩
    refine ⟨(e L).val, ?_, (mem_glFunctionals_iff_entrywise (ψ.scale a) π _).mp (e L).property⟩
    intro h
    have hL : e L = 0 := Subtype.ext h
    have : L = 0 := e.injective (hL.trans e.map_zero.symm)
    exact hne (congrArg Subtype.val this)
  · rintro ⟨ℓ, hne, hℓ⟩
    let L : glFunctionals (ψ.scale a) n π :=
      ⟨ℓ, (mem_glFunctionals_iff_entrywise (ψ.scale a) π ℓ).mpr hℓ⟩
    refine ⟨(e.symm L).val, ?_, (mem_glFunctionals_iff_entrywise ψ π _).mp (e.symm L).property⟩
    intro h
    have hL : e.symm L = 0 := Subtype.ext h
    have : L = 0 := e.symm.injective (hL.trans e.symm.map_zero.symm)
    exact hne (congrArg Subtype.val this)

/-- Inversion of the raw character preserves nonzero functional existence on
one and the same representation. -/
theorem entrywise_exists_inverse_iff (ψ : UnitaryAdditiveCharacter K)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V) :
    (∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ EntrywiseEquivariant π ψ.complex ℓ) ↔
    ∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ EntrywiseEquivariant π ψ.complex⁻¹ ℓ := by
  simpa only [scale_neg_one_complex] using entrywise_exists_scale_iff ψ π (-1)

/-- Raw-character version of character inversion, with the target hypotheses. -/
theorem raw_exists_inverse_iff (ψ : AddChar K ℂ) (hc : Continuous ψ) (hne : ψ ≠ 1)
    (hu : ∀ x, ‖ψ x‖ = 1)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V) :
    (∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ EntrywiseEquivariant π ψ ℓ) ↔
    ∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ EntrywiseEquivariant π ψ⁻¹ ℓ :=
  entrywise_exists_inverse_iff (UnitaryAdditiveCharacter.ofComplex ψ hc hne hu) π

omit [IsTopologicalRing K] in
/-- Raw-character version of coefficient injectivity, for the target equation. -/
theorem raw_coefficient_injective (ψ : AddChar K ℂ) (hc : Continuous ψ) (hne : ψ ≠ 1)
    (hu : ∀ x, ‖ψ x‖ = 1)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V)
    [Representation.IsIrreducible π] (ℓ : Module.Dual ℂ V) (hℓne : ℓ ≠ 0)
    (hℓ : EntrywiseEquivariant π ψ ℓ) :
    Function.Injective (fun v => fun g => ℓ (π g v)) :=
  entrywise_coefficient_injective (UnitaryAdditiveCharacter.ofComplex ψ hc hne hu) π ℓ hℓne hℓ

end Field

end Langlands.Whittaker
