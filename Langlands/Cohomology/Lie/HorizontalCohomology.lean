import Langlands.Cohomology.Lie.HorizontalDifferential
import Langlands.Cohomology.Lie.CoefficientSquareZeroProof
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Cohomology of the actual horizontal full-group differential -/

noncomputable section

namespace Langlands.Cohomology.Lie.Horizontal

universe u v w ug

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

/-- The published actual restricted coefficient differential, in all degrees. -/
abbrev differential (q : ℕ) : C q →ₗ[K] C (q + 1) :=
  horizontalEquivariantDifferential H σ ρ hσ hρ q (hι q)

local notation "D" => differential H σ ρ hσ hρ hι

/-- Square zero is inherited from the actual coefficient differential. -/
@[simp]
theorem differential_differential (q : ℕ) (f : C q) :
    D (q + 1) (D q f) = 0 := by
  apply Subtype.ext
  exact Langlands.Cohomology.Lie.differential_differential q f.val

/-- Closed cochains inside the actual horizontal full-group submodule. -/
def cycles (q : ℕ) : Submodule K (C q) := LinearMap.ker (D q)

/-- Actual boundaries, with zero boundaries in degree zero. -/
def boundaries : (q : ℕ) → Submodule K (C q)
  | 0 => ⊥
  | q + 1 => LinearMap.range (D q)

local notation "Z" => cycles H σ ρ hσ hρ hι
local notation "B" => boundaries H σ ρ hσ hρ hι

local instance (q : ℕ) : AddCommGroup (Z q) := Submodule.addCommGroup _

@[simp] theorem mem_cycles {q : ℕ} {f : C q} :
    f ∈ Z q ↔ D q f = 0 := Iff.rfl

@[simp] theorem boundaries_zero : B 0 = ⊥ := rfl

@[simp] theorem boundaries_succ (q : ℕ) : B (q + 1) = LinearMap.range (D q) := rfl

@[simp] theorem mem_boundaries_zero {f : C 0} : f ∈ B 0 ↔ f = 0 :=
  Submodule.mem_bot K

@[simp] theorem mem_boundaries_succ {q : ℕ} {f : C (q + 1)} :
    f ∈ B (q + 1) ↔ ∃ g : C q, D q g = f := Iff.rfl

/-- The published square-zero theorem proves the inclusion of boundaries. -/
theorem boundaries_le_cycles (q : ℕ) : B q ≤ Z q := by
  cases q with
  | zero => exact bot_le
  | succ q =>
    rintro f ⟨g, rfl⟩
    exact differential_differential H σ ρ hσ hρ hι q g

/-- The range of the actual boundary inclusion inside cycles. -/
def boundariesInCycles (q : ℕ) : Submodule K (Z q) :=
  LinearMap.range (Submodule.inclusion (boundaries_le_cycles H σ ρ hσ hρ hι q))

local notation "BZ" => boundariesInCycles H σ ρ hσ hρ hι

/-- The quotient of the actual closed horizontal cochains by actual boundaries. -/
abbrev HorizontalCohomology (q : ℕ) := Z q ⧸ BZ q

/-- The quotient projection from closed horizontal cochains. -/
def cohomologyClass (q : ℕ) : Z q →ₗ[K] HorizontalCohomology H σ ρ hσ hρ hι q := (BZ q).mkQ

@[simp] theorem mem_boundariesInCycles {q : ℕ} {f : Z q} :
    f ∈ BZ q ↔ f.val ∈ B q := by
  constructor
  · rintro ⟨g, rfl⟩
    exact g.property
  · intro hf
    exact ⟨⟨f.val, hf⟩, Subtype.ext rfl⟩

theorem cohomologyClass_surjective (q : ℕ) :
    Function.Surjective (cohomologyClass H σ ρ hσ hρ hι q) := (BZ q).mkQ_surjective

/-- A cycle has zero class exactly when it is an actual horizontal boundary. -/
@[simp] theorem cohomologyClass_eq_zero {q : ℕ} (f : Z q) :
    cohomologyClass H σ ρ hσ hρ hι q f = 0 ↔ f.val ∈ B q := by
  exact (Submodule.Quotient.mk_eq_zero (BZ q)).trans
    (mem_boundariesInCycles H σ ρ hσ hρ hι)

/-- Equality of classes means that the difference is an actual boundary. -/
theorem cohomologyClass_eq_iff {q : ℕ} (f g : Z q) :
    cohomologyClass H σ ρ hσ hρ hι q f = cohomologyClass H σ ρ hσ hρ hι q g ↔
      f.val - g.val ∈ B q := by
  exact (Submodule.Quotient.eq (BZ q)).trans
    (mem_boundariesInCycles H σ ρ hσ hρ hι)

/-- The actual horizontal differential with its codomain restricted to cycles. -/
def coboundaryToCycles (q : ℕ) : C q →ₗ[K] Z (q + 1) :=
  (D q).codRestrict (Z (q + 1)) (differential_differential H σ ρ hσ hρ hι q)

@[simp] theorem coboundaryToCycles_val (q : ℕ) (f : C q) :
    (coboundaryToCycles H σ ρ hσ hρ hι q f).val = D q f := rfl

@[simp] theorem cohomologyClass_coboundary (q : ℕ) (f : C q) :
    cohomologyClass H σ ρ hσ hρ hι (q + 1)
      (coboundaryToCycles H σ ρ hσ hρ hι q f) = 0 := by
  apply (cohomologyClass_eq_zero H σ ρ hσ hρ hι _).mpr
  exact ⟨f, rfl⟩

end Langlands.Cohomology.Lie.Horizontal
