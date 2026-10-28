import Langlands.Cohomology.Lie.HorizontalCohomology

/-! # Actions on the actual horizontal cohomology quotient -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Cohomology.Lie.Horizontal

universe u v w ug up

variable {K : Type u} [Field K] [CharZero K]
variable {L : Type v} [LieRing L] [LieAlgebra K L]
variable {M : Type w} [AddCommGroup M] [Module K M]
variable [LieRingModule L M] [LieModule K L M]
variable {G : Type ug} [Group G]

variable (H : Submodule K L) (σ : Representation K G L) (ρ : Representation K G M)
variable (hσ : ∀ g x y, σ g ⁅x, y⁆ = ⁅σ g x, σ g y⁆)
variable (hρ : ∀ g x m, ρ g ⁅x, m⁆ = ⁅σ g x, ρ g m⁆)
variable (hι : ∀ q, ∀ f ∈ Langlands.HorizontalAlternating.submodule H σ ρ q,
  ∀ y ∈ H, ∀ x : Fin q → L,
    ⁅y, f x⁆ = ∑ i, f (Function.update x i ⁅y, x i⁆))

local notation "C" => Langlands.HorizontalAlternating.submodule H σ ρ
local notation "D" => differential H σ ρ hσ hρ hι
local notation "Z" => cycles H σ ρ hσ hρ hι
local notation "B" => boundaries H σ ρ hσ hρ hι
local notation "BZ" => boundariesInCycles H σ ρ hσ hρ hι

local instance (q : ℕ) : AddCommGroup (C q) := Submodule.addCommGroup _

local instance (q : ℕ) : AddCommGroup (Z q) := Submodule.addCommGroup _

variable {P : Type up} [Monoid P]
variable (action : (q : ℕ) → Representation K P
  (Langlands.HorizontalAlternating.submodule H σ ρ q))
variable (hAction : ∀ (q : ℕ) (p : P)
  (f : Langlands.HorizontalAlternating.submodule H σ ρ q),
  differential H σ ρ hσ hρ hι q (action q p f) =
    action (q + 1) p (differential H σ ρ hσ hρ hι q f))

include hAction

/-- A cochain action commuting with the actual differential preserves cycles. -/
theorem action_mem_cycles (q : ℕ) (p : P) (f : C q) (hf : f ∈ Z q) :
    action q p f ∈ Z q := by
  change D q f = 0 at hf
  change D q (action q p f) = 0
  rw [hAction q p f, hf, map_zero]

/-- The same cochain action preserves the actual image boundaries in each degree. -/
theorem action_mem_boundaries (q : ℕ) (p : P) (f : C q) (hf : f ∈ B q) :
    action q p f ∈ B q := by
  cases q with
  | zero =>
    change f = 0 at hf
    change action 0 p f = 0
    rw [hf, map_zero]
  | succ q =>
    obtain ⟨g, rfl⟩ := hf
    exact ⟨action q p g, hAction q p g⟩

/-- Restrict the cochain action to the actual closed horizontal cochains. -/
def cyclesRepresentation (q : ℕ) : Representation K P (Z q) :=
  (action q).subrepresentation (Z q) (action_mem_cycles H σ ρ hσ hρ hι action hAction q)

@[simp] theorem cyclesRepresentation_val (q : ℕ) (p : P) (f : Z q) :
    (cyclesRepresentation H σ ρ hσ hρ hι action hAction q p f).val = action q p f.val := rfl

/-- The restricted action preserves boundaries inside cycles. -/
theorem cyclesRepresentation_mem_boundariesInCycles (q : ℕ) (p : P)
    (f : Z q) (hf : f ∈ BZ q) :
    cyclesRepresentation H σ ρ hσ hρ hι action hAction q p f ∈ BZ q := by
  apply (mem_boundariesInCycles H σ ρ hσ hρ hι).mpr
  exact action_mem_boundaries H σ ρ hσ hρ hι action hAction q p f.val
    ((mem_boundariesInCycles H σ ρ hσ hρ hι).mp hf)

/-- The induced representation on the existing horizontal cohomology quotient. -/
def cohomologyRepresentation (q : ℕ) :
    Representation K P (HorizontalCohomology H σ ρ hσ hρ hι q) :=
  (cyclesRepresentation H σ ρ hσ hρ hι action hAction q).quotient (BZ q)
    (cyclesRepresentation_mem_boundariesInCycles H σ ρ hσ hρ hι action hAction q)

/-- The action on a class is represented by the same cochain action. -/
@[simp] theorem cohomologyRepresentation_class (q : ℕ) (p : P) (f : Z q) :
    cohomologyRepresentation H σ ρ hσ hρ hι action hAction q p
        (cohomologyClass H σ ρ hσ hρ hι q f) =
      cohomologyClass H σ ρ hσ hρ hι q
        (cyclesRepresentation H σ ρ hσ hρ hι action hAction q p f) := rfl

/-- The quotient projection is an intertwiner for the constructed actions. -/
def cohomologyClassIntertwiner (q : ℕ) :
    (cyclesRepresentation H σ ρ hσ hρ hι action hAction q).IntertwiningMap
      (cohomologyRepresentation H σ ρ hσ hρ hι action hAction q) where
  toLinearMap := cohomologyClass H σ ρ hσ hρ hι q
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

@[simp] theorem cohomologyClassIntertwiner_toLinearMap (q : ℕ) :
    (cohomologyClassIntertwiner H σ ρ hσ hρ hι action hAction q).toLinearMap =
      cohomologyClass H σ ρ hσ hρ hι q := rfl

end Langlands.Cohomology.Lie.Horizontal
