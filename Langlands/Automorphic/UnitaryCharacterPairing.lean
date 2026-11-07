import Langlands.Global.LeftCosetSpace
import Langlands.Representation.Unitary.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # The pairing of functions with a common unitary character on a left quotient

For a topological group `H`, a subgroup `Γ₀`, a subgroup `Z` and a unitary character
`ω : Z →* Circle`, the continuous functions on `H` that are left `Γ₀`-invariant and transform
by `ω` under left multiplication by `Z` form a subrepresentation of positive right translation.
For two such functions `f` and `g`, the products `conj f * g` and `‖f‖` are left invariant under
`Z ⊔ Γ₀` and descend to the actual left quotient `(Z ⊔ Γ₀) \ H`. Integrating the descended
product against a right-invariant measure gives an invariant positive definite Hermitian form
on the functions whose descended absolute value is square integrable. No centrality of `Z`
and no universe restriction on `H` is used.
-/

noncomputable section

universe u v w

open MeasureTheory ComplexConjugate

namespace Langlands.Automorphic.UnitaryCharacterPairing

open Langlands.Global

section RightAction

variable {H : Type u} [Group H] [TopologicalSpace H] [ContinuousMul H]

variable (H) in
/-- Positive right translation on continuous complex functions on `H`. -/
def rightAction : Representation ℂ H C(H, ℂ) where
  toFun g :=
    { toFun f := f.comp ⟨fun x => x * g, continuous_mul_const g⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply ContinuousMap.ext
    intro x
    simp
  map_mul' g g' := by
    apply LinearMap.ext
    intro f
    apply ContinuousMap.ext
    intro x
    simp [mul_assoc]

@[simp]
theorem rightAction_apply (g : H) (f : C(H, ℂ)) (x : H) :
    rightAction H g f x = f (x * g) := rfl

end RightAction

section Stabilizer

variable {H : Type u} [Group H]

/-- The elements whose left multiplication leaves a function unchanged. -/
def leftStabilizer {E : Type v} (h : H → E) : Subgroup H where
  carrier := {γ | ∀ x, h (γ * x) = h x}
  one_mem' x := by simp
  mul_mem' {a b} ha hb x := by
    rw [mul_assoc, ha, hb]
  inv_mem' {a} ha x := by
    have hx := ha (a⁻¹ * x)
    rw [mul_inv_cancel_left] at hx
    exact hx.symm

theorem mem_leftStabilizer {E : Type v} (h : H → E) (γ : H) :
    γ ∈ leftStabilizer h ↔ ∀ x, h (γ * x) = h x := Iff.rfl

/-- A function fixed by left multiplication by two subgroups is fixed by their supremum. -/
theorem sup_le_leftStabilizer {E : Type v} (Γ₀ Z : Subgroup H) (h : H → E)
    (hΓ : ∀ γ ∈ Γ₀, ∀ x, h (γ * x) = h x) (hZ : ∀ z ∈ Z, ∀ x, h (z * x) = h x) :
    Z ⊔ Γ₀ ≤ leftStabilizer h :=
  sup_le hZ hΓ

end Stabilizer

section Descent

variable {H : Type u} [Group H] [TopologicalSpace H]
variable (Γ₀ Z : Subgroup H)

/-- A continuous function fixed by left multiplication by `Z ⊔ Γ₀`, as a continuous function on
the actual left quotient. -/
def descend {E : Type v} [TopologicalSpace E] (h : C(H, E))
    (hh : Z ⊔ Γ₀ ≤ leftStabilizer h) : C(LeftCosetSpace (Z ⊔ Γ₀), E) :=
  ⟨LeftCosetSpace.lift (Z ⊔ Γ₀) h (fun γ x => hh γ.property x),
    LeftCosetSpace.continuous_lift (Z ⊔ Γ₀) h _ h.continuous⟩

@[simp]
theorem descend_mk {E : Type v} [TopologicalSpace E] (h : C(H, E))
    (hh : Z ⊔ Γ₀ ≤ leftStabilizer h) (x : H) :
    descend Γ₀ Z h hh (LeftCosetSpace.mk (Z ⊔ Γ₀) x) = h x := rfl

end Descent

/-- A unit complex number times its conjugate is one. -/
theorem conj_mul_circle (z : Circle) : conj (z : ℂ) * z = 1 := by
  rw [Complex.conj_mul', Circle.norm_coe]
  simp

section Character

variable {H : Type u} [Group H] [TopologicalSpace H] [ContinuousMul H]
variable (Γ₀ Z : Subgroup H) (ω : Z →* Circle)

/-- Continuous functions invariant under left multiplication by `Γ₀` and transforming by the
unitary character `ω` under left multiplication by `Z`. -/
def characterSubmodule : Submodule ℂ C(H, ℂ) where
  carrier := {f | (∀ γ ∈ Γ₀, ∀ x, f (γ * x) = f x) ∧
    ∀ (z : Z) (x : H), f ((z : H) * x) = (ω z : ℂ) * f x}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ => by simp⟩
  add_mem' {f g} hf hg := by
    refine ⟨fun γ hγ x => ?_, fun z x => ?_⟩
    · simp [hf.1 γ hγ x, hg.1 γ hγ x]
    · simp [hf.2 z x, hg.2 z x, mul_add]
  smul_mem' c f hf := by
    refine ⟨fun γ hγ x => ?_, fun z x => ?_⟩
    · simp [hf.1 γ hγ x]
    · simp only [ContinuousMap.smul_apply, smul_eq_mul, hf.2 z x]
      ring

omit [ContinuousMul H] in
theorem mem_characterSubmodule (f : C(H, ℂ)) :
    f ∈ characterSubmodule Γ₀ Z ω ↔
      (∀ γ ∈ Γ₀, ∀ x, f (γ * x) = f x) ∧
        ∀ (z : Z) (x : H), f ((z : H) * x) = (ω z : ℂ) * f x := Iff.rfl

/-- The character condition is stable under positive right translation. -/
def characterSubrepresentation : Subrepresentation (rightAction H) where
  toSubmodule := characterSubmodule Γ₀ Z ω
  apply_mem_toSubmodule g f hf := by
    refine ⟨fun γ hγ x => ?_, fun z x => ?_⟩
    · simp only [rightAction_apply, mul_assoc]
      exact hf.1 γ hγ (x * g)
    · simp only [rightAction_apply, mul_assoc]
      exact hf.2 z (x * g)

/-- Continuous functions with left `Γ₀`-invariance and `Z`-character `ω`. -/
abbrev CharacterFunctions := (characterSubrepresentation Γ₀ Z ω).toSubmodule

/-- Positive right translation on functions with character `ω`. -/
def characterAction : Representation ℂ H (CharacterFunctions Γ₀ Z ω) :=
  (characterSubrepresentation Γ₀ Z ω).toRepresentation

variable {Γ₀ Z ω}

@[simp]
theorem characterAction_apply (g : H) (f : CharacterFunctions Γ₀ Z ω) (x : H) :
    (characterAction Γ₀ Z ω g f).val x = f.val (x * g) := rfl

theorem CharacterFunctions.rational (f : CharacterFunctions Γ₀ Z ω) {γ : H} (hγ : γ ∈ Γ₀)
    (x : H) : f.val (γ * x) = f.val x :=
  f.property.1 γ hγ x

theorem CharacterFunctions.character (f : CharacterFunctions Γ₀ Z ω) (z : Z) (x : H) :
    f.val ((z : H) * x) = (ω z : ℂ) * f.val x :=
  f.property.2 z x

variable (Γ₀ Z ω)

/-- The continuous function `x ↦ conj (f x) * g x` on `H`. -/
def pairingIntegrand (f g : CharacterFunctions Γ₀ Z ω) : C(H, ℂ) :=
  ⟨fun x => conj (f.val x) * g.val x,
    (Complex.continuous_conj.comp f.val.continuous).mul g.val.continuous⟩

theorem pairingIntegrand_le_leftStabilizer (f g : CharacterFunctions Γ₀ Z ω) :
    Z ⊔ Γ₀ ≤ leftStabilizer (pairingIntegrand Γ₀ Z ω f g) := by
  apply sup_le_leftStabilizer
  · intro γ hγ x
    change conj (f.val (γ * x)) * g.val (γ * x) = conj (f.val x) * g.val x
    rw [CharacterFunctions.rational f hγ, CharacterFunctions.rational g hγ]
  · intro z hz x
    have hf : f.val (z * x) = (ω ⟨z, hz⟩ : ℂ) * f.val x :=
      CharacterFunctions.character f ⟨z, hz⟩ x
    have hg : g.val (z * x) = (ω ⟨z, hz⟩ : ℂ) * g.val x :=
      CharacterFunctions.character g ⟨z, hz⟩ x
    change conj (f.val (z * x)) * g.val (z * x) = conj (f.val x) * g.val x
    rw [hf, hg, map_mul]
    calc conj (ω ⟨z, hz⟩ : ℂ) * conj (f.val x) * ((ω ⟨z, hz⟩ : ℂ) * g.val x)
        = (conj (ω ⟨z, hz⟩ : ℂ) * (ω ⟨z, hz⟩ : ℂ)) * (conj (f.val x) * g.val x) := by ring
      _ = conj (f.val x) * g.val x := by rw [conj_mul_circle, one_mul]

/-- The continuous function `x ↦ ‖f x‖` on `H`. -/
def normIntegrand (f : CharacterFunctions Γ₀ Z ω) : C(H, ℝ) :=
  ⟨fun x => ‖f.val x‖, continuous_norm.comp f.val.continuous⟩

theorem normIntegrand_le_leftStabilizer (f : CharacterFunctions Γ₀ Z ω) :
    Z ⊔ Γ₀ ≤ leftStabilizer (normIntegrand Γ₀ Z ω f) := by
  apply sup_le_leftStabilizer
  · intro γ hγ x
    change ‖f.val (γ * x)‖ = ‖f.val x‖
    rw [CharacterFunctions.rational f hγ]
  · intro z hz x
    have hf : f.val (z * x) = (ω ⟨z, hz⟩ : ℂ) * f.val x :=
      CharacterFunctions.character f ⟨z, hz⟩ x
    change ‖f.val (z * x)‖ = ‖f.val x‖
    rw [hf, norm_mul, Circle.norm_coe, one_mul]

/-- The descended product `conj f * g` on the actual quotient `(Z ⊔ Γ₀) \ H`. -/
def pairingDensity (f g : CharacterFunctions Γ₀ Z ω) : C(LeftCosetSpace (Z ⊔ Γ₀), ℂ) :=
  descend Γ₀ Z (pairingIntegrand Γ₀ Z ω f g) (pairingIntegrand_le_leftStabilizer Γ₀ Z ω f g)

/-- The descended absolute value `‖f‖` on the actual quotient `(Z ⊔ Γ₀) \ H`. -/
def normDensity (f : CharacterFunctions Γ₀ Z ω) : C(LeftCosetSpace (Z ⊔ Γ₀), ℝ) :=
  descend Γ₀ Z (normIntegrand Γ₀ Z ω f) (normIntegrand_le_leftStabilizer Γ₀ Z ω f)

@[simp]
theorem pairingDensity_mk (f g : CharacterFunctions Γ₀ Z ω) (x : H) :
    pairingDensity Γ₀ Z ω f g (LeftCosetSpace.mk (Z ⊔ Γ₀) x) = conj (f.val x) * g.val x := rfl

@[simp]
theorem normDensity_mk (f : CharacterFunctions Γ₀ Z ω) (x : H) :
    normDensity Γ₀ Z ω f (LeftCosetSpace.mk (Z ⊔ Γ₀) x) = ‖f.val x‖ := rfl

theorem normDensity_nonneg (f : CharacterFunctions Γ₀ Z ω) (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    0 ≤ normDensity Γ₀ Z ω f q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  exact norm_nonneg (f.val x : ℂ)

theorem norm_pairingDensity (f g : CharacterFunctions Γ₀ Z ω) (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    ‖pairingDensity Γ₀ Z ω f g q‖ = normDensity Γ₀ Z ω f q * normDensity Γ₀ Z ω g q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  rw [pairingDensity_mk, normDensity_mk, normDensity_mk, norm_mul, Complex.norm_conj]

theorem pairingDensity_self (f : CharacterFunctions Γ₀ Z ω) (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    pairingDensity Γ₀ Z ω f f q = ((normDensity Γ₀ Z ω f q ^ 2 : ℝ) : ℂ) := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  simp [Complex.conj_mul']

theorem pairingDensity_conj (f g : CharacterFunctions Γ₀ Z ω) (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    conj (pairingDensity Γ₀ Z ω g f q) = pairingDensity Γ₀ Z ω f g q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  simp [mul_comm]

theorem pairingDensity_add_left (f f' g : CharacterFunctions Γ₀ Z ω)
    (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    pairingDensity Γ₀ Z ω (f + f') g q =
      pairingDensity Γ₀ Z ω f g q + pairingDensity Γ₀ Z ω f' g q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  simp [add_mul]

theorem pairingDensity_smul_left (c : ℂ) (f g : CharacterFunctions Γ₀ Z ω)
    (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    pairingDensity Γ₀ Z ω (c • f) g q = conj c * pairingDensity Γ₀ Z ω f g q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  simp [mul_assoc]

theorem pairingDensity_add_right (f g g' : CharacterFunctions Γ₀ Z ω)
    (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    pairingDensity Γ₀ Z ω f (g + g') q =
      pairingDensity Γ₀ Z ω f g q + pairingDensity Γ₀ Z ω f g' q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  simp [mul_add]

theorem pairingDensity_smul_right (c : ℂ) (f g : CharacterFunctions Γ₀ Z ω)
    (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    pairingDensity Γ₀ Z ω f (c • g) q = c * pairingDensity Γ₀ Z ω f g q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  simp only [pairingDensity_mk, SetLike.val_smul, ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem normDensity_add_le (f f' : CharacterFunctions Γ₀ Z ω) (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    normDensity Γ₀ Z ω (f + f') q ≤ normDensity Γ₀ Z ω f q + normDensity Γ₀ Z ω f' q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  simpa using norm_add_le (f.val x) (f'.val x)

theorem normDensity_smul (c : ℂ) (f : CharacterFunctions Γ₀ Z ω)
    (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    normDensity Γ₀ Z ω (c • f) q = ‖c‖ * normDensity Γ₀ Z ω f q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  simp

theorem normDensity_zero (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    normDensity Γ₀ Z ω 0 q = 0 := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  simp

/-- Right translation of both functions is right translation of the descended product. -/
theorem pairingDensity_characterAction (g : H) (f f' : CharacterFunctions Γ₀ Z ω)
    (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    pairingDensity Γ₀ Z ω (characterAction Γ₀ Z ω g f) (characterAction Γ₀ Z ω g f') q =
      pairingDensity Γ₀ Z ω f f' (LeftCosetSpace.rightTranslate (Z ⊔ Γ₀) g q) := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  rfl

/-- Right translation of a function is right translation of its descended absolute value. -/
theorem normDensity_characterAction (g : H) (f : CharacterFunctions Γ₀ Z ω)
    (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    normDensity Γ₀ Z ω (characterAction Γ₀ Z ω g f) q =
      normDensity Γ₀ Z ω f (LeftCosetSpace.rightTranslate (Z ⊔ Γ₀) g q) := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  rfl

/-- A function with vanishing descended absolute value is zero. -/
theorem eq_zero_of_normDensity_eq_zero (f : CharacterFunctions Γ₀ Z ω)
    (hf : ∀ q, normDensity Γ₀ Z ω f q = 0) : f = 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  exact norm_eq_zero.mp (hf (LeftCosetSpace.mk (Z ⊔ Γ₀) x))

end Character

section L2

variable {H : Type u} [Group H] [TopologicalSpace H] [ContinuousMul H]
variable (Γ₀ Z : Subgroup H) (ω : Z →* Circle)
variable [MeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))]
  [OpensMeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))]
variable (μ : Measure (LeftCosetSpace (Z ⊔ Γ₀)))

/-- Every actual right translation of the quotient preserves the measure. -/
def RightInvariant : Prop :=
  ∀ g : H, MeasurePreserving (LeftCosetSpace.rightTranslate (Z ⊔ Γ₀) g) μ μ

/-- Functions with character `ω` whose descended absolute value is square integrable. -/
def l2CharacterSubmodule : Submodule ℂ (CharacterFunctions Γ₀ Z ω) where
  carrier := {f | MemLp (normDensity Γ₀ Z ω f) 2 μ}
  zero_mem' := by
    change MemLp (normDensity Γ₀ Z ω 0) 2 μ
    have h : (normDensity Γ₀ Z ω 0 : LeftCosetSpace (Z ⊔ Γ₀) → ℝ) = 0 :=
      funext (normDensity_zero Γ₀ Z ω)
    rw [h]
    exact MemLp.zero
  add_mem' {f f'} hf hf' := by
    change MemLp (normDensity Γ₀ Z ω (f + f')) 2 μ
    refine (MemLp.add hf hf').mono (normDensity Γ₀ Z ω (f + f')).continuous.aestronglyMeasurable
      (ae_of_all _ fun q => ?_)
    rw [Real.norm_of_nonneg (normDensity_nonneg Γ₀ Z ω _ q), Pi.add_apply,
      Real.norm_of_nonneg (add_nonneg (normDensity_nonneg Γ₀ Z ω _ q)
        (normDensity_nonneg Γ₀ Z ω _ q))]
    exact normDensity_add_le Γ₀ Z ω f f' q
  smul_mem' c f hf := by
    change MemLp (normDensity Γ₀ Z ω (c • f)) 2 μ
    have h : (normDensity Γ₀ Z ω (c • f) : LeftCosetSpace (Z ⊔ Γ₀) → ℝ) =
        fun q => ‖c‖ * normDensity Γ₀ Z ω f q :=
      funext (normDensity_smul Γ₀ Z ω c f)
    rw [h]
    exact hf.const_mul ‖c‖

theorem mem_l2CharacterSubmodule (f : CharacterFunctions Γ₀ Z ω) :
    f ∈ l2CharacterSubmodule Γ₀ Z ω μ ↔ MemLp (normDensity Γ₀ Z ω f) 2 μ := Iff.rfl

/-- Square integrability of the descended absolute value is stable under right translation. -/
def l2CharacterSubrepresentation (hμ : RightInvariant Γ₀ Z μ) :
    Subrepresentation (characterAction Γ₀ Z ω) where
  toSubmodule := l2CharacterSubmodule Γ₀ Z ω μ
  apply_mem_toSubmodule g f hf := by
    change MemLp (normDensity Γ₀ Z ω (characterAction Γ₀ Z ω g f)) 2 μ
    have h : (normDensity Γ₀ Z ω (characterAction Γ₀ Z ω g f) :
        LeftCosetSpace (Z ⊔ Γ₀) → ℝ) =
        (normDensity Γ₀ Z ω f) ∘ LeftCosetSpace.rightTranslate (Z ⊔ Γ₀) g :=
      funext (normDensity_characterAction Γ₀ Z ω g f)
    rw [h]
    exact MemLp.comp_measurePreserving hf (hμ g)

/-- Continuous functions on `H` with character `ω` whose descended absolute value is square
integrable, as a submodule of all continuous functions. -/
def l2Submodule : Submodule ℂ C(H, ℂ) :=
  (l2CharacterSubmodule Γ₀ Z ω μ).map (CharacterFunctions Γ₀ Z ω).subtype

theorem mem_l2Submodule (f : C(H, ℂ)) :
    f ∈ l2Submodule Γ₀ Z ω μ ↔ ∃ hf : f ∈ characterSubmodule Γ₀ Z ω,
      MemLp (normDensity Γ₀ Z ω ⟨f, hf⟩) 2 μ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hf, hf'⟩
    exact ⟨⟨f, hf⟩, hf', rfl⟩

theorem l2Submodule_le_characterSubmodule :
    l2Submodule Γ₀ Z ω μ ≤ characterSubmodule Γ₀ Z ω := by
  rintro _ ⟨y, -, rfl⟩
  exact y.property

/-- Square-integrable functions with character `ω` are stable under positive right
translation. -/
def l2Subrepresentation (hμ : RightInvariant Γ₀ Z μ) : Subrepresentation (rightAction H) where
  toSubmodule := l2Submodule Γ₀ Z ω μ
  apply_mem_toSubmodule g f hf := by
    obtain ⟨y, hy, rfl⟩ := hf
    exact ⟨characterAction Γ₀ Z ω g y,
      (l2CharacterSubrepresentation Γ₀ Z ω μ hμ).apply_mem_toSubmodule g hy, rfl⟩

/-- Continuous functions on `H` with character `ω` whose descended absolute value is square
integrable. -/
abbrev L2Functions (hμ : RightInvariant Γ₀ Z μ) := (l2Subrepresentation Γ₀ Z ω μ hμ).toSubmodule

/-- Square-integrable functions with character `ω`, with positive right translation. -/
def l2Action (hμ : RightInvariant Γ₀ Z μ) : Representation ℂ H (L2Functions Γ₀ Z ω μ hμ) :=
  (l2Subrepresentation Γ₀ Z ω μ hμ).toRepresentation

@[simp]
theorem l2Action_apply (hμ : RightInvariant Γ₀ Z μ) (g : H) (f : L2Functions Γ₀ Z ω μ hμ)
    (x : H) : (l2Action Γ₀ Z ω μ hμ g f).val x = f.val (x * g) := rfl

variable {Γ₀ Z ω μ}

/-- A square-integrable function with character `ω`, as a function with character `ω`. -/
def toCharacter {hμ : RightInvariant Γ₀ Z μ} (f : L2Functions Γ₀ Z ω μ hμ) :
    CharacterFunctions Γ₀ Z ω :=
  ⟨f.val, l2Submodule_le_characterSubmodule Γ₀ Z ω μ f.property⟩

theorem toCharacter_mem {hμ : RightInvariant Γ₀ Z μ}
    (f : L2Functions Γ₀ Z ω μ hμ) : toCharacter f ∈ l2CharacterSubmodule Γ₀ Z ω μ := by
  obtain ⟨y, hy, hyf⟩ := Submodule.mem_map.mp f.property
  have h : toCharacter f = y := Subtype.ext hyf.symm
  rw [h]
  exact hy

@[simp]
theorem toCharacter_val {hμ : RightInvariant Γ₀ Z μ}
    (f : L2Functions Γ₀ Z ω μ hμ) : (toCharacter f).val = f.val := rfl

theorem toCharacter_l2Action {hμ : RightInvariant Γ₀ Z μ} (g : H)
    (f : L2Functions Γ₀ Z ω μ hμ) :
    toCharacter (l2Action Γ₀ Z ω μ hμ g f) = characterAction Γ₀ Z ω g (toCharacter f) := rfl

theorem toCharacter_add {hμ : RightInvariant Γ₀ Z μ} (f f' : L2Functions Γ₀ Z ω μ hμ) :
    toCharacter (f + f') = toCharacter f + toCharacter f' := rfl

theorem toCharacter_smul {hμ : RightInvariant Γ₀ Z μ} (c : ℂ) (f : L2Functions Γ₀ Z ω μ hμ) :
    toCharacter (c • f) = c • toCharacter f := rfl

theorem toCharacter_zero {hμ : RightInvariant Γ₀ Z μ} :
    toCharacter (0 : L2Functions Γ₀ Z ω μ hμ) = 0 := rfl

theorem toCharacter_injective {hμ : RightInvariant Γ₀ Z μ} :
    Function.Injective (toCharacter (Γ₀ := Γ₀) (Z := Z) (ω := ω) (hμ := hμ)) := by
  intro f f' h
  apply Subtype.ext
  have h' := congrArg (fun x : CharacterFunctions Γ₀ Z ω => x.val) h
  exact h'

/-- The descended product of two square-integrable functions is integrable, by Hölder. -/
theorem integrable_pairingDensity {f g : CharacterFunctions Γ₀ Z ω}
    (hf : f ∈ l2CharacterSubmodule Γ₀ Z ω μ) (hg : g ∈ l2CharacterSubmodule Γ₀ Z ω μ) :
    Integrable (pairingDensity Γ₀ Z ω f g) μ := by
  have hfg : Integrable (⇑(normDensity Γ₀ Z ω f) * ⇑(normDensity Γ₀ Z ω g)) μ :=
    MemLp.integrable_mul (p := 2) (q := 2) hf hg
  refine hfg.mono' (pairingDensity Γ₀ Z ω f g).continuous.aestronglyMeasurable
    (ae_of_all _ fun q => ?_)
  rw [norm_pairingDensity]
  rfl

variable (Γ₀ Z ω μ)

/-- The integral `∫ conj f * g` of the descended product over the quotient. -/
def pairing (f g : CharacterFunctions Γ₀ Z ω) : ℂ :=
  ∫ q, pairingDensity Γ₀ Z ω f g q ∂μ

omit [OpensMeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))] in
theorem pairing_def (f g : CharacterFunctions Γ₀ Z ω) :
    pairing Γ₀ Z ω μ f g = ∫ q, pairingDensity Γ₀ Z ω f g q ∂μ := rfl

omit [OpensMeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))] in
theorem pairing_conj (f g : CharacterFunctions Γ₀ Z ω) :
    conj (pairing Γ₀ Z ω μ g f) = pairing Γ₀ Z ω μ f g := by
  rw [pairing, pairing, ← integral_conj]
  exact integral_congr_ae (ae_of_all _ (pairingDensity_conj Γ₀ Z ω f g))

omit [OpensMeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))] in
theorem pairing_self (f : CharacterFunctions Γ₀ Z ω) :
    pairing Γ₀ Z ω μ f f = ((∫ q, normDensity Γ₀ Z ω f q ^ 2 ∂μ : ℝ) : ℂ) := by
  have h := integral_complex_ofReal (μ := μ) (f := fun q => normDensity Γ₀ Z ω f q ^ 2)
  rw [pairing, ← h]
  exact integral_congr_ae (ae_of_all _ (pairingDensity_self Γ₀ Z ω f))

omit [OpensMeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))] in
theorem re_pairing_self_nonneg (f : CharacterFunctions Γ₀ Z ω) :
    0 ≤ (pairing Γ₀ Z ω μ f f).re := by
  rw [pairing_self, Complex.ofReal_re]
  exact integral_nonneg fun q => sq_nonneg _

variable {Γ₀ Z ω μ}

theorem pairing_add_left {f f' g : CharacterFunctions Γ₀ Z ω}
    (hf : f ∈ l2CharacterSubmodule Γ₀ Z ω μ) (hf' : f' ∈ l2CharacterSubmodule Γ₀ Z ω μ)
    (hg : g ∈ l2CharacterSubmodule Γ₀ Z ω μ) :
    pairing Γ₀ Z ω μ (f + f') g = pairing Γ₀ Z ω μ f g + pairing Γ₀ Z ω μ f' g := by
  rw [pairing, pairing, pairing, ← integral_add (integrable_pairingDensity hf hg)
    (integrable_pairingDensity hf' hg)]
  exact integral_congr_ae (ae_of_all _ (pairingDensity_add_left Γ₀ Z ω f f' g))

theorem pairing_add_right {f g g' : CharacterFunctions Γ₀ Z ω}
    (hf : f ∈ l2CharacterSubmodule Γ₀ Z ω μ) (hg : g ∈ l2CharacterSubmodule Γ₀ Z ω μ)
    (hg' : g' ∈ l2CharacterSubmodule Γ₀ Z ω μ) :
    pairing Γ₀ Z ω μ f (g + g') = pairing Γ₀ Z ω μ f g + pairing Γ₀ Z ω μ f g' := by
  rw [pairing, pairing, pairing, ← integral_add (integrable_pairingDensity hf hg)
    (integrable_pairingDensity hf hg')]
  exact integral_congr_ae (ae_of_all _ (pairingDensity_add_right Γ₀ Z ω f g g'))

variable (Γ₀ Z ω μ)

omit [OpensMeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))] in
theorem pairing_smul_left (c : ℂ) (f g : CharacterFunctions Γ₀ Z ω) :
    pairing Γ₀ Z ω μ (c • f) g = conj c * pairing Γ₀ Z ω μ f g := by
  rw [pairing, pairing, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ (pairingDensity_smul_left Γ₀ Z ω c f g))

omit [OpensMeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))] in
theorem pairing_smul_right (c : ℂ) (f g : CharacterFunctions Γ₀ Z ω) :
    pairing Γ₀ Z ω μ f (c • g) = c * pairing Γ₀ Z ω μ f g := by
  rw [pairing, pairing, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ (pairingDensity_smul_right Γ₀ Z ω c f g))

/-- Right translation of both functions preserves the pairing. -/
theorem pairing_characterAction (hμ : RightInvariant Γ₀ Z μ) (g : H)
    (f f' : CharacterFunctions Γ₀ Z ω) :
    pairing Γ₀ Z ω μ (characterAction Γ₀ Z ω g f) (characterAction Γ₀ Z ω g f') =
      pairing Γ₀ Z ω μ f f' := by
  rw [pairing, pairing]
  have h : (fun q => pairingDensity Γ₀ Z ω (characterAction Γ₀ Z ω g f)
      (characterAction Γ₀ Z ω g f') q) =
      fun q => pairingDensity Γ₀ Z ω f f' (LeftCosetSpace.rightTranslate (Z ⊔ Γ₀) g q) :=
    funext (pairingDensity_characterAction Γ₀ Z ω g f f')
  rw [h, ← integral_map (hμ g).measurable.aemeasurable, (hμ g).map_eq]
  rw [(hμ g).map_eq]
  exact (pairingDensity Γ₀ Z ω f f').continuous.aestronglyMeasurable

variable [μ.IsOpenPosMeasure]

/-- For a measure positive on nonempty open sets, the pairing is definite on square-integrable
functions. -/
theorem eq_zero_of_pairing_self_eq_zero {f : CharacterFunctions Γ₀ Z ω}
    (hf : f ∈ l2CharacterSubmodule Γ₀ Z ω μ) (h0 : pairing Γ₀ Z ω μ f f = 0) : f = 0 := by
  rw [pairing_self, Complex.ofReal_eq_zero] at h0
  have hint : Integrable (fun q => normDensity Γ₀ Z ω f q ^ 2) μ := MemLp.integrable_sq hf
  have hae := (integral_eq_zero_iff_of_nonneg (fun q => sq_nonneg _) hint).mp h0
  have hcont : Continuous (fun q => normDensity Γ₀ Z ω f q ^ 2) :=
    (normDensity Γ₀ Z ω f).continuous.pow 2
  have heq := (hcont.ae_eq_iff_eq μ continuous_const).mp hae
  apply eq_zero_of_normDensity_eq_zero Γ₀ Z ω f
  intro q
  have hq := congrFun heq q
  exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hq

end L2

section Form

variable {H : Type u} [Group H] [TopologicalSpace H] [ContinuousMul H]
variable (Γ₀ Z : Subgroup H) (ω : Z →* Circle)
variable [MeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))]
  [OpensMeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))]
variable (μ : Measure (LeftCosetSpace (Z ⊔ Γ₀))) (hμ : RightInvariant Γ₀ Z μ)

/-- The pairing on square-integrable functions with character `ω`, conjugate-linear in the
first argument and linear in the second. -/
def sesquilinearPairing :
    L2Functions Γ₀ Z ω μ hμ →ₗ⋆[ℂ] L2Functions Γ₀ Z ω μ hμ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun f g => pairing Γ₀ Z ω μ (toCharacter f) (toCharacter g))
    (fun f f' g => by
      rw [toCharacter_add]
      exact pairing_add_left (toCharacter_mem f) (toCharacter_mem f') (toCharacter_mem g))
    (fun c f g => by
      rw [toCharacter_smul]
      exact pairing_smul_left Γ₀ Z ω μ c (toCharacter f) (toCharacter g))
    (fun f g g' => by
      rw [toCharacter_add]
      exact pairing_add_right (toCharacter_mem f) (toCharacter_mem g) (toCharacter_mem g'))
    (fun c f g => by
      rw [toCharacter_smul]
      exact pairing_smul_right Γ₀ Z ω μ c (toCharacter f) (toCharacter g))

@[simp]
theorem sesquilinearPairing_apply (f g : L2Functions Γ₀ Z ω μ hμ) :
    sesquilinearPairing Γ₀ Z ω μ hμ f g =
      ∫ q, pairingDensity Γ₀ Z ω (toCharacter f) (toCharacter g) q ∂μ := rfl

variable [μ.IsOpenPosMeasure]

/-- The invariant positive definite Hermitian form `⟨f, g⟩ = ∫ conj f * g` on square-integrable
functions with character `ω`, for the actual positive right translation action. -/
def invariantPositiveForm :
    InvariantPositiveForm (V := L2Functions Γ₀ Z ω μ hμ) (l2Action Γ₀ Z ω μ hμ) where
  inner f g := pairing Γ₀ Z ω μ (toCharacter f) (toCharacter g)
  conj_inner_symm f g := pairing_conj Γ₀ Z ω μ (toCharacter f) (toCharacter g)
  re_inner_nonneg f := re_pairing_self_nonneg Γ₀ Z ω μ (toCharacter f)
  add_left f f' g := by
    change pairing Γ₀ Z ω μ (toCharacter (f + f')) (toCharacter g) = _
    rw [toCharacter_add]
    exact pairing_add_left (toCharacter_mem f) (toCharacter_mem f') (toCharacter_mem g)
  smul_left f g c := by
    change pairing Γ₀ Z ω μ (toCharacter (c • f)) (toCharacter g) = _
    rw [toCharacter_smul]
    exact pairing_smul_left Γ₀ Z ω μ c (toCharacter f) (toCharacter g)
  definite f hf := by
    apply toCharacter_injective
    rw [toCharacter_zero]
    exact eq_zero_of_pairing_self_eq_zero Γ₀ Z ω μ (toCharacter_mem f) hf
  invariant g f f' := by
    change pairing Γ₀ Z ω μ (toCharacter (l2Action Γ₀ Z ω μ hμ g f))
      (toCharacter (l2Action Γ₀ Z ω μ hμ g f')) = pairing Γ₀ Z ω μ (toCharacter f) (toCharacter f')
    rw [toCharacter_l2Action, toCharacter_l2Action]
    exact pairing_characterAction Γ₀ Z ω μ hμ g (toCharacter f) (toCharacter f')

@[simp]
theorem invariantPositiveForm_inner (f g : L2Functions Γ₀ Z ω μ hμ) :
    (invariantPositiveForm Γ₀ Z ω μ hμ).inner f g =
      ∫ q, pairingDensity Γ₀ Z ω (toCharacter f) (toCharacter g) q ∂μ := rfl

theorem isUnitarizable_l2Action :
    IsUnitarizable (V := L2Functions Γ₀ Z ω μ hμ) (l2Action Γ₀ Z ω μ hμ) :=
  ⟨invariantPositiveForm Γ₀ Z ω μ hμ⟩

/-- The same form is invariant for the action of any monoid through a homomorphism to `H`, for
example a finite adelic subgroup. -/
def invariantPositiveFormComp {K : Type w} [Monoid K] (φ : K →* H) :
    InvariantPositiveForm (V := L2Functions Γ₀ Z ω μ hμ) ((l2Action Γ₀ Z ω μ hμ).comp φ) where
  toInnerProductCore := (invariantPositiveForm Γ₀ Z ω μ hμ).toInnerProductCore
  invariant k f f' := (invariantPositiveForm Γ₀ Z ω μ hμ).invariant (φ k) f f'

@[simp]
theorem invariantPositiveFormComp_inner {K : Type w} [Monoid K] (φ : K →* H)
    (f g : L2Functions Γ₀ Z ω μ hμ) :
    (invariantPositiveFormComp Γ₀ Z ω μ hμ φ).inner f g =
      ∫ q, pairingDensity Γ₀ Z ω (toCharacter f) (toCharacter g) q ∂μ := rfl

theorem isUnitarizable_l2Action_comp {K : Type w} [Monoid K] (φ : K →* H) :
    IsUnitarizable (V := L2Functions Γ₀ Z ω μ hμ) ((l2Action Γ₀ Z ω μ hμ).comp φ) :=
  ⟨invariantPositiveFormComp Γ₀ Z ω μ hμ φ⟩

end Form

end Langlands.Automorphic.UnitaryCharacterPairing
