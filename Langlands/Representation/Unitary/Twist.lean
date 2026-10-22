import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Twist.Definitions

/-!
# Invariant positive forms under unit-modulus scalar twists

The underlying Hermitian form is unchanged. No finite-dimensionality, topology,
or completeness assumption on the representation carrier is needed.
-/

namespace Langlands

universe uG uV

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

private theorem inner_twist_eq (χ : G →* ℂˣ) (hχ : ∀ g, ‖(χ g : ℂ)‖ = 1)
    (ρ : Representation ℂ G V) (b : InnerProductSpace.Core ℂ V)
    (g : G) (v w : V) :
    b.inner (Langlands.twist χ ρ g v) (Langlands.twist χ ρ g w) =
      b.inner (ρ g v) (ρ g w) := by
  let := b
  change b.inner ((χ g : ℂ) • ρ g v) ((χ g : ℂ) • ρ g w) = _
  rw [b.smul_left]
  rw [show b.inner (ρ g v) ((χ g : ℂ) • ρ g w) =
    (χ g : ℂ) * b.inner (ρ g v) (ρ g w) from
      InnerProductSpace.Core.inner_smul_right _ _]
  rw [← mul_assoc, Complex.conj_mul', hχ g]
  simp

namespace InvariantPositiveForm

variable (χ : G →* ℂˣ) (hχ : ∀ g, ‖(χ g : ℂ)‖ = 1)
  {ρ : Representation ℂ G V}

/-- A unit-modulus twist preserves the given positive invariant form. -/
def twist (b : InvariantPositiveForm ρ) :
    InvariantPositiveForm (Langlands.twist χ ρ) where
  toInnerProductCore := b.toInnerProductCore
  invariant g v w :=
    (inner_twist_eq χ hχ ρ b.toInnerProductCore g v w).trans (b.invariant g v w)

/-- The same positive form is invariant before a unit-modulus twist. -/
def untwist (b : InvariantPositiveForm (Langlands.twist χ ρ)) :
    InvariantPositiveForm ρ where
  toInnerProductCore := b.toInnerProductCore
  invariant g v w :=
    (inner_twist_eq χ hχ ρ b.toInnerProductCore g v w).symm.trans (b.invariant g v w)

@[simp]
theorem twist_inner (b : InvariantPositiveForm ρ) (v w : V) :
    (b.twist χ hχ).inner v w = b.inner v w := rfl

@[simp]
theorem untwist_inner (b : InvariantPositiveForm (Langlands.twist χ ρ)) (v w : V) :
    (b.untwist χ hχ).inner v w = b.inner v w := rfl

@[simp]
theorem untwist_twist (b : InvariantPositiveForm ρ) :
    (b.twist χ hχ).untwist χ hχ = b := rfl

@[simp]
theorem twist_untwist (b : InvariantPositiveForm (Langlands.twist χ ρ)) :
    (b.untwist χ hχ).twist χ hχ = b := rfl

/-- Unit-modulus twisting gives a bijection of actual invariant positive forms. -/
def twistEquiv (ρ : Representation ℂ G V) :
    InvariantPositiveForm ρ ≃ InvariantPositiveForm (Langlands.twist χ ρ) where
  toFun := twist χ hχ
  invFun := untwist χ hχ
  left_inv := untwist_twist χ hχ
  right_inv := twist_untwist χ hχ

end InvariantPositiveForm

/-- Unit-modulus scalar twisting preserves and reflects unitarizability on any carrier. -/
theorem isUnitarizable_twist_iff (χ : G →* ℂˣ) (hχ : ∀ g, ‖(χ g : ℂ)‖ = 1)
    (ρ : Representation ℂ G V) :
    IsUnitarizable (twist χ ρ) ↔ IsUnitarizable ρ := by
  constructor
  · rintro ⟨b⟩
    exact ⟨b.untwist χ hχ⟩
  · rintro ⟨b⟩
    exact ⟨b.twist χ hχ⟩

end Langlands
