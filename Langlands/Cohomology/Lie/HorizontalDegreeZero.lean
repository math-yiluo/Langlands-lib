import Langlands.Cohomology.Lie.HorizontalCohomology
import Mathlib.Algebra.Lie.Abelian

/-! # Degree zero of the original horizontal cohomology quotient -/

noncomputable section

namespace Langlands.Cohomology.Lie.Horizontal

universe u v w ug

variable {K : Type u} [Field K] [CharZero K]
variable {L : Type v} [LieRing L] [LieAlgebra K L]
variable {M : Type w} [AddCommGroup M] [Module K M]
variable [LieRingModule L M] [LieModule K L M]
variable {G : Type ug} [Group G]

/-- Vectors fixed by the full group and annihilated by the full Lie algebra. -/
def jointInvariants (ρ : Representation K G M) : Submodule K M :=
  ρ.invariants ⊓ (LieModule.maxTrivSubmodule K L M).toSubmodule

omit [CharZero K] in
@[simp] theorem mem_jointInvariants (ρ : Representation K G M) (m : M) :
    m ∈ jointInvariants (L := L) ρ ↔
      (∀ g, ρ g m = m) ∧ (∀ x : L, ⁅x, m⁆ = 0) := Iff.rfl

variable (H : Submodule K L) (σ : Representation K G L) (ρ : Representation K G M)
variable (hσ : ∀ g x y, σ g ⁅x, y⁆ = ⁅σ g x, σ g y⁆)
variable (hρ : ∀ g x m, ρ g ⁅x, m⁆ = ⁅σ g x, ρ g m⁆)
variable (hι : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ ρ q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))

local notation "C" => Langlands.HorizontalAlternating.submodule H σ ρ
local notation "D" => differential H σ ρ hσ hρ hι
local notation "Z" => cycles H σ ρ hσ hρ hι
local notation "BZ" => boundariesInCycles H σ ρ hσ hρ hι

local instance instAddCommGroupCycles_lieHorizontalDegreeZero (q : ℕ) :
    AddCommGroup (Z q) := Submodule.addCommGroup _

/-- Evaluation of the actual restricted differential on a zero cochain. -/
theorem differential_zero_apply (f : C 0) (x : Fin 1 → L) :
    (D 0 f).val x = ⁅x 0, f.val 0⁆ := by
  change Langlands.Cohomology.Lie.differential 0 f.val x = _
  rw [Langlands.Cohomology.Lie.differential_apply_zero]
  exact congrArg (fun z : Fin 0 → L => ⁅x 0, f.val z⁆) (Subsingleton.elim _ _)

/-- Closed zero cochains are precisely those killed by every Lie direction. -/
theorem mem_cycles_zero_iff (f : C 0) :
    f ∈ Z 0 ↔ ∀ x : L, ⁅x, f.val 0⁆ = 0 := by
  change D 0 f = 0 ↔ _
  constructor
  · intro hf x
    have hx := congrArg (fun z : C 1 => z.val (fun _ => x)) hf
    rw [differential_zero_apply] at hx
    exact hx
  · intro hf
    apply Subtype.ext
    apply AlternatingMap.ext
    intro x
    change (D 0 f).val x = 0
    rw [differential_zero_apply, hf]

/-- The existing zero-cochain fixed-vector equivalence restricted to actual cycles. -/
def cyclesDegreeZeroEquiv : Z 0 ≃ₗ[K] jointInvariants (L := L) ρ where
  toFun f := ⟨(Langlands.HorizontalAlternating.degreeZeroEquiv H σ ρ f.val).val,
    (Langlands.HorizontalAlternating.degreeZeroEquiv H σ ρ f.val).property,
    (mem_cycles_zero_iff H σ ρ hσ hρ hι f.val).mp f.property⟩
  invFun m :=
    ⟨(Langlands.HorizontalAlternating.degreeZeroEquiv H σ ρ).symm
        ⟨m.val, m.property.1⟩,
      (mem_cycles_zero_iff H σ ρ hσ hρ hι _).mpr m.property.2⟩
  left_inv f := by
    apply Subtype.ext
    exact (Langlands.HorizontalAlternating.degreeZeroEquiv H σ ρ).symm_apply_apply f.val
  right_inv m := by
    apply Subtype.ext
    rfl
  map_add' f g := rfl
  map_smul' a f := rfl

@[simp] theorem cyclesDegreeZeroEquiv_apply (f : Z 0) :
    (cyclesDegreeZeroEquiv H σ ρ hσ hρ hι f).val = f.val.val 0 := rfl

/-- The inverse really is a constant zero cochain on the original carrier. -/
@[simp] theorem cyclesDegreeZeroEquiv_symm_apply
    (m : jointInvariants (L := L) ρ) (x : Fin 0 → L) :
    ((cyclesDegreeZeroEquiv H σ ρ hσ hρ hι).symm m).val.val x = m.val := rfl

/-- In degree zero the original submodule of boundaries inside cycles is zero. -/
@[simp] theorem boundariesInCycles_zero : BZ 0 = ⊥ := by
  apply le_antisymm
  · intro f hf
    have hz : f.val = 0 :=
      (mem_boundaries_zero H σ ρ hσ hρ hι).mp
        ((mem_boundariesInCycles H σ ρ hσ hρ hι).mp hf)
    exact (Submodule.mem_bot K).mpr (Subtype.ext hz)
  · exact bot_le

/-- Identify the original degree-zero quotient with simultaneous fixed vectors. -/
def degreeZeroEquiv :
    HorizontalCohomology H σ ρ hσ hρ hι 0 ≃ₗ[K] jointInvariants (L := L) ρ :=
  ((BZ 0).quotEquivOfEqBot (boundariesInCycles_zero H σ ρ hσ hρ hι)).trans
    (cyclesDegreeZeroEquiv H σ ρ hσ hρ hι)

/-- A class is sent to the value of its original zero-cochain representative. -/
@[simp] theorem degreeZeroEquiv_class (f : Z 0) :
    (degreeZeroEquiv H σ ρ hσ hρ hι
      (cohomologyClass H σ ρ hσ hρ hι 0 f)).val = f.val.val 0 := rfl

/-- A simultaneous invariant is represented by the constant zero cochain. -/
@[simp] theorem degreeZeroEquiv_symm (m : jointInvariants (L := L) ρ) :
    (degreeZeroEquiv H σ ρ hσ hρ hι).symm m =
      cohomologyClass H σ ρ hσ hρ hι 0
        ((cyclesDegreeZeroEquiv H σ ρ hσ hρ hι).symm m) := rfl

/-- Nonzero simultaneous invariants give nonzero classes in the original quotient. -/
theorem degreeZeroEquiv_symm_ne_zero (m : jointInvariants (L := L) ρ)
    (hm : m.val ≠ 0) :
    (degreeZeroEquiv H σ ρ hσ hρ hι).symm m ≠ 0 := by
  intro hz
  have hmzero : m = 0 :=
    (degreeZeroEquiv H σ ρ hσ hρ hι).symm.injective
      (hz.trans (map_zero (degreeZeroEquiv H σ ρ hσ hρ hι).symm).symm)
  exact hm (congrArg Subtype.val hmzero)

end Langlands.Cohomology.Lie.Horizontal
