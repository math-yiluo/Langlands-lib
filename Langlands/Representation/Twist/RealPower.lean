import Langlands.Representation.Twist.SmoothProof
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Complex.Basic

/-!
# Real powers of positive characters

The input is a genuine positive character. Its identification with the normalized
determinant absolute value for a local field is a separate construction.
-/

noncomputable section

open scoped NNReal

namespace Langlands

universe uG uV uW

/-- Embed a positive real unit as a complex unit. -/
def positiveUnitsToComplex : ℝ≥0ˣ →* ℂˣ :=
  Units.map (Complex.ofRealHom.toMonoidHom.comp
    (Nonneg.coeRingHom : ℝ≥0 →+* ℝ).toMonoidHom)

@[simp]
theorem coe_positiveUnitsToComplex (x : ℝ≥0ˣ) :
    (positiveUnitsToComplex x : ℂ) = ((x : ℝ≥0) : ℝ) := rfl

variable {G : Type uG} [Group G]

/-- The character `g ↦ ν(g)^s`, with positive real powers embedded in complex units. -/
def realPowerCharacter (ν : G →* ℝ≥0ˣ) (s : ℝ) : G →* ℂˣ :=
  (positiveUnitsToComplex.comp (Units.map (NNReal.rpowMonoidHom s))).comp ν

@[simp]
theorem coe_realPowerCharacter (ν : G →* ℝ≥0ˣ) (s : ℝ) (g : G) :
    (realPowerCharacter ν s g : ℂ) = ((((ν g : ℝ≥0) : ℝ) ^ s : ℝ) : ℂ) := rfl

@[simp]
theorem realPowerCharacter_zero (ν : G →* ℝ≥0ˣ) :
    realPowerCharacter ν 0 = 1 := by
  ext g
  simp

@[simp]
theorem realPowerCharacter_one (ν : G →* ℝ≥0ˣ) :
    realPowerCharacter ν 1 = positiveUnitsToComplex.comp ν := by
  ext g
  simp

theorem realPowerCharacter_add (ν : G →* ℝ≥0ˣ) (s t : ℝ) :
    realPowerCharacter ν (s + t) = realPowerCharacter ν s * realPowerCharacter ν t := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  simp only [MonoidHom.mul_apply, Units.val_mul, coe_realPowerCharacter]
  rw [Real.rpow_add (by exact_mod_cast (pos_iff_ne_zero.mpr (ν g).ne_zero))]
  simp

theorem realPowerCharacter_neg (ν : G →* ℝ≥0ˣ) (s : ℝ) :
    realPowerCharacter ν (-s) = (realPowerCharacter ν s)⁻¹ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, coe_realPowerCharacter]
  rw [Real.rpow_neg (ν g : ℝ≥0).coe_nonneg]
  simp

theorem ker_le_realPowerCharacter_ker (ν : G →* ℝ≥0ˣ) (s : ℝ) :
    ν.ker ≤ (realPowerCharacter ν s).ker := by
  intro g hg
  change ν g = 1 at hg
  change realPowerCharacter ν s g = 1
  simp [realPowerCharacter, hg]

theorem isOpen_ker_realPowerCharacter [TopologicalSpace G] [SeparatelyContinuousMul G]
    (ν : G →* ℝ≥0ˣ) (hν : IsOpen (ν.ker : Set G)) (s : ℝ) :
    IsOpen ((realPowerCharacter ν s).ker : Set G) :=
  Subgroup.isOpen_mono (ker_le_realPowerCharacter_ker ν s) hν

variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Twist a complex representation by the real power of a positive character. -/
def realPowerTwist (ν : G →* ℝ≥0ˣ) (s : ℝ) (ρ : Representation ℂ G V) :
    Representation ℂ G V :=
  twist (realPowerCharacter ν s) ρ

@[simp]
theorem realPowerTwist_apply (ν : G →* ℝ≥0ˣ) (s : ℝ)
    (ρ : Representation ℂ G V) (g : G) (v : V) :
    realPowerTwist ν s ρ g v = ((((ν g : ℝ≥0) : ℝ) ^ s : ℝ) : ℂ) • ρ g v := rfl

@[simp]
theorem realPowerTwist_zero (ν : G →* ℝ≥0ˣ) (ρ : Representation ℂ G V) :
    realPowerTwist ν 0 ρ = ρ := by
  ext g v
  simp

theorem realPowerTwist_add (ν : G →* ℝ≥0ˣ) (s t : ℝ)
    (ρ : Representation ℂ G V) :
    realPowerTwist ν (s + t) ρ = realPowerTwist ν s (realPowerTwist ν t ρ) := by
  ext g v
  change (realPowerCharacter ν (s + t) g : ℂ) • ρ g v =
    (realPowerCharacter ν s g : ℂ) • ((realPowerCharacter ν t g : ℂ) • ρ g v)
  rw [realPowerCharacter_add]
  simp only [MonoidHom.mul_apply, Units.val_mul, smul_smul]

@[simp]
theorem realPowerTwist_neg_cancel (ν : G →* ℝ≥0ˣ) (s : ℝ)
    (ρ : Representation ℂ G V) :
    realPowerTwist ν (-s) (realPowerTwist ν s ρ) = ρ := by
  rw [← realPowerTwist_add, neg_add_cancel, realPowerTwist_zero]

@[simp]
theorem realPowerTwist_cancel_neg (ν : G →* ℝ≥0ˣ) (s : ℝ)
    (ρ : Representation ℂ G V) :
    realPowerTwist ν s (realPowerTwist ν (-s) ρ) = ρ := by
  rw [← realPowerTwist_add, add_neg_cancel, realPowerTwist_zero]

/-- The ordinary scalar-twist equivalence on intertwiner spaces, specialized to real powers. -/
def realPowerTwistIntertwiningEquiv (ν : G →* ℝ≥0ˣ) (s : ℝ)
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    ρ.IntertwiningMap σ ≃ₗ[ℂ]
      (realPowerTwist ν s ρ).IntertwiningMap (realPowerTwist ν s σ) :=
  twistIntertwiningEquiv (realPowerCharacter ν s) ρ σ

/-- Real-power twisting transports actual representation equivalences. -/
def realPowerTwistEquiv (ν : G →* ℝ≥0ˣ) (s : ℝ)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) :
    (realPowerTwist ν s ρ).Equiv (realPowerTwist ν s σ) :=
  twistEquiv (realPowerCharacter ν s) e

theorem isSmooth_realPowerTwist_iff [TopologicalSpace G] [SeparatelyContinuousMul G]
    (ν : G →* ℝ≥0ˣ) (hν : IsOpen (ν.ker : Set G)) (s : ℝ)
    (ρ : Representation ℂ G V) :
    IsSmooth (realPowerTwist ν s ρ) ↔ IsSmooth ρ :=
  isSmooth_twist_iff (realPowerCharacter ν s) ρ (isOpen_ker_realPowerCharacter ν hν s)

end Langlands
