import Langlands.HarmonicAnalysis.Basic

/-!
# Continuous characters for the FML conductor interface

Adapted by Worker 20 from Fukuhiro Ueda, epsilon_FML, commit
0b4159be50e1bd45ddff1de4280399576a3e2024 (Apache-2.0).
Modifications: project namespace and imports, minimal constructor API,
transparent reuse of Library quasicharacters, and a new unitary-character bridge.
See Characters.md and LICENSE for provenance and the retained license.
-/

namespace Langlands.FML

universe u
noncomputable section

/-- The total complex phase, with value one at zero. -/
def phase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    phase z = z / (‖z‖ : ℂ) := by simp [phase, hz]

/-- A continuous additive character with nonzero complex values. -/
def ContinuousAddChar (A : Type u) [AddMonoid A] [TopologicalSpace A] :=
  {ψ : AddChar A ℂˣ // Continuous ψ}

/-- A continuous quasi-character on the unit group, with values in `ℂˣ`. -/
abbrev ContinuousQuasiChar (F : Type u) [Monoid F] [TopologicalSpace F] :=
  ContinuousMonoidHom Fˣ ℂˣ

private def continuousAddCharSubmonoid (A : Type u)
    [AddMonoid A] [TopologicalSpace A] : Submonoid (AddChar A ℂˣ) where
  carrier := {ψ | Continuous ψ}
  one_mem' := continuous_const
  mul_mem' hψ hφ := hψ.mul hφ

private def continuousAddCharSubgroup (A : Type u)
    [AddCommGroup A] [TopologicalSpace A] : Subgroup (AddChar A ℂˣ) where
  carrier := {ψ | Continuous ψ}
  one_mem' := continuous_const
  mul_mem' hψ hφ := hψ.mul hφ
  inv_mem' {ψ} hψ := by
    change Continuous (fun x : A => (ψ⁻¹ : AddChar A ℂˣ) x)
    simpa only [AddChar.inv_apply'] using hψ.fun_inv

/-- Continuous additive characters form a commutative monoid under pointwise
multiplication. -/
instance {A : Type u} [AddMonoid A] [TopologicalSpace A] :
    CommMonoid (ContinuousAddChar A) :=
  inferInstanceAs (CommMonoid (continuousAddCharSubmonoid A))

/-- Continuous additive characters on an additive commutative group form a
commutative group under pointwise multiplication. -/
instance {A : Type u} [AddCommGroup A] [TopologicalSpace A] :
    CommGroup (ContinuousAddChar A) :=
  inferInstanceAs (CommGroup (continuousAddCharSubgroup A))

/-- A continuous additive character evaluates as a function into `ℂˣ`. -/
instance {A : Type u} [AddMonoid A] [TopologicalSpace A] :
    FunLike (ContinuousAddChar A) A ℂˣ where
  coe ψ := ψ.1
  coe_injective ψ φ h :=
    Subtype.ext (AddChar.ext ψ.1 φ.1 fun x => congr_fun h x)

/-- Evaluation of a continuous additive character is continuous. -/
instance {A : Type u} [AddMonoid A] [TopologicalSpace A] :
    ContinuousMapClass (ContinuousAddChar A) A ℂˣ where
  map_continuous ψ := ψ.2

namespace ContinuousAddChar

/-- Continuous additive characters are equal when all their values agree. -/
@[ext]
theorem ext {A : Type u} [AddMonoid A] [TopologicalSpace A]
    {ψ φ : ContinuousAddChar A} (h : ∀ x, ψ x = φ x) : ψ = φ :=
  DFunLike.ext ψ φ h

/-- The underlying Mathlib additive character. -/
def toAddChar {A : Type u} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) : AddChar A ℂˣ :=
  ψ.1

@[simp]
theorem toAddChar_apply {A : Type u} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) (x : A) : ψ.toAddChar x = ψ x :=
  rfl

/-- An additive character maps zero to one. -/
@[simp]
theorem map_zero_eq_one {A : Type u} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) : ψ 0 = 1 :=
  AddChar.map_zero_eq_one ψ.toAddChar

/-- An additive character turns addition into multiplication. -/
theorem map_add_eq_mul {A : Type u} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) (x y : A) : ψ (x + y) = ψ x * ψ y :=
  AddChar.map_add_eq_mul ψ.toAddChar x y

/-- The unit-valued evaluation map of a continuous additive character is
continuous. -/
theorem continuous {A : Type u} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) : Continuous ψ :=
  map_continuous ψ

@[simp] theorem one_apply {A : Type u} [AddMonoid A] [TopologicalSpace A] (x : A) :
    (1 : ContinuousAddChar A) x = 1 := rfl

end ContinuousAddChar

/-- On fields this is definitionally the existing Library quasicharacter type. -/
abbrev quasicharacterIdentification (F : Type u) [Field F] [TopologicalSpace F] :
    HarmonicAnalysis.Quasicharacter F → ContinuousQuasiChar F := id

/-- Injectivity of the actual Mathlib circle-to-units map. -/
theorem circle_toUnits_injective : Function.Injective Circle.toUnits :=
  unitSphereToUnits_injective

/-- Transport a Library character through the inclusion of the circle into units. -/
def ofUnitaryAdditiveCharacter {A : Type u} [AddGroup A] [TopologicalSpace A]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter A) : ContinuousAddChar A := by
  refine ⟨Circle.toUnits.compAddChar ψ.toAddChar, ?_⟩
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val.comp ψ.continuous_toFun
  · change Continuous (fun x => ((ψ x : ℂ)⁻¹))
    exact (continuous_subtype_val.comp ψ.continuous_toFun).inv₀
      (fun x => Circle.coe_ne_zero (ψ x))

@[simp] theorem ofUnitaryAdditiveCharacter_apply {A : Type u}
    [AddGroup A] [TopologicalSpace A]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter A) (x : A) :
    ofUnitaryAdditiveCharacter ψ x = Circle.toUnits (ψ x) := rfl

@[simp] theorem ofUnitaryAdditiveCharacter_coe_apply {A : Type u}
    [AddGroup A] [TopologicalSpace A]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter A) (x : A) :
    (ofUnitaryAdditiveCharacter ψ x : ℂ) = (ψ x : ℂ) := rfl

/-- Nontriviality survives the injective inclusion into complex units. -/
theorem ofUnitaryAdditiveCharacter_ne_one {A : Type u}
    [AddGroup A] [TopologicalSpace A]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter A) :
    ofUnitaryAdditiveCharacter ψ ≠ 1 := by
  intro h
  apply ψ.nontrivial
  apply AddChar.ext
  intro x
  apply circle_toUnits_injective
  simpa only [ofUnitaryAdditiveCharacter_apply, ContinuousAddChar.one_apply,
    AddChar.one_apply, map_one] using congrArg (fun φ : ContinuousAddChar A => φ x) h

end
end Langlands.FML
