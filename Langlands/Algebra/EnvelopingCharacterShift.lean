import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.Basic

/-! # Shifting an enveloping algebra by a linear form vanishing on brackets

Let `L` be a complex Lie algebra and `μ : L → ℂ` a linear form with `μ ⁅U, V⁆ = 0`. The map
`U ↦ U + μ(U)` is a Lie homomorphism into the enveloping algebra, so it extends to an algebra
endomorphism `shift μ` of `U(L)`. The shifts by `μ` and `-μ` are inverse to each other, so
`shift μ` is an automorphism and maps the center onto itself.

If a Lie homomorphism `ρ : L → A` into an associative algebra and an element `T ∈ A` satisfy
`ρ(U) T = T (ρ(U) + μ(U))` for all `U` (for instance multiplication by a character, whose
derivative is `μ`), then `ρ(y) T = T ρ(shift μ y)` for every `y ∈ U(L)`; if moreover
`T ≠ 0` and `A` is torsion free over `ℂ`, then `μ` vanishes on brackets automatically. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Algebra.EnvelopingCharacterShift

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

local notation "UL" => UniversalEnvelopingAlgebra ℂ L

section Shift

variable (μ : L →ₗ[ℂ] ℂ)

/-- The Lie map `U ↦ U + μ(U)` into the enveloping algebra, for a linear form `μ` vanishing on
brackets. -/
def shiftLie (hμ : ∀ U V : L, μ ⁅U, V⁆ = 0) : L →ₗ⁅ℂ⁆ UL :=
  { (UniversalEnvelopingAlgebra.ι ℂ (L := L)).toLinearMap +
      (Algebra.linearMap ℂ UL).comp μ with
    map_lie' := by
      intro U V
      change UniversalEnvelopingAlgebra.ι ℂ ⁅U, V⁆ + algebraMap ℂ UL (μ ⁅U, V⁆) =
        (UniversalEnvelopingAlgebra.ι ℂ U + algebraMap ℂ UL (μ U)) *
            (UniversalEnvelopingAlgebra.ι ℂ V + algebraMap ℂ UL (μ V)) -
          (UniversalEnvelopingAlgebra.ι ℂ V + algebraMap ℂ UL (μ V)) *
            (UniversalEnvelopingAlgebra.ι ℂ U + algebraMap ℂ UL (μ U))
      rw [hμ, map_zero, add_zero, LieHom.map_lie, LieRing.of_associative_ring_bracket]
      have h1 := Algebra.commutes (μ U) (UniversalEnvelopingAlgebra.ι ℂ V : UL)
      have h2 := Algebra.commutes (μ V) (UniversalEnvelopingAlgebra.ι ℂ U : UL)
      have h3 : algebraMap ℂ UL (μ U) * algebraMap ℂ UL (μ V) =
          algebraMap ℂ UL (μ V) * algebraMap ℂ UL (μ U) :=
        ((Commute.all (μ U) (μ V)).map (algebraMap ℂ UL)).eq
      rw [add_mul, add_mul, mul_add, mul_add, mul_add, mul_add, h1, h2, h3]
      abel }

/-- The algebra endomorphism of the enveloping algebra extending `U ↦ U + μ(U)`. -/
def shift (hμ : ∀ U V : L, μ ⁅U, V⁆ = 0) : UL →ₐ[ℂ] UL :=
  UniversalEnvelopingAlgebra.lift ℂ (shiftLie μ hμ)

@[simp]
theorem shift_ι (hμ : ∀ U V : L, μ ⁅U, V⁆ = 0) (U : L) :
    shift μ hμ (UniversalEnvelopingAlgebra.ι ℂ U) =
      UniversalEnvelopingAlgebra.ι ℂ U + algebraMap ℂ UL (μ U) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ (shiftLie μ hμ) U

theorem neg_lie_eq_zero (hμ : ∀ U V : L, μ ⁅U, V⁆ = 0) (U V : L) : (-μ) ⁅U, V⁆ = 0 := by
  rw [LinearMap.neg_apply, hμ, neg_zero]

/-- The shift by `μ` is a left inverse of the shift by `-μ`. -/
theorem shift_comp_neg (hμ : ∀ U V : L, μ ⁅U, V⁆ = 0) :
    (shift μ hμ).comp (shift (-μ) (neg_lie_eq_zero μ hμ)) = AlgHom.id ℂ UL := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro U
  change shift μ hμ (shift (-μ) (neg_lie_eq_zero μ hμ) (UniversalEnvelopingAlgebra.ι ℂ U)) =
    UniversalEnvelopingAlgebra.ι ℂ U
  rw [shift_ι, map_add, shift_ι, AlgHom.commutes, LinearMap.neg_apply, map_neg, add_assoc,
    add_neg_cancel, add_zero]

/-- The shift is surjective. -/
theorem shift_surjective (hμ : ∀ U V : L, μ ⁅U, V⁆ = 0) : Function.Surjective (shift μ hμ) :=
  fun a => ⟨shift (-μ) (neg_lie_eq_zero μ hμ) a, AlgHom.congr_fun (shift_comp_neg μ hμ) a⟩

/-- The shift maps central elements to central elements. -/
theorem shift_mem_center (hμ : ∀ U V : L, μ ⁅U, V⁆ = 0) {z : UL}
    (hz : z ∈ Subalgebra.center ℂ UL) : shift μ hμ z ∈ Subalgebra.center ℂ UL := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro a
  obtain ⟨b, rfl⟩ := shift_surjective μ hμ a
  rw [← map_mul, ← map_mul, hz b]

/-- The shift restricted to the center, as an algebra endomorphism of the center. -/
def centerShift (hμ : ∀ U V : L, μ ⁅U, V⁆ = 0) :
    Subalgebra.center ℂ UL →ₐ[ℂ] Subalgebra.center ℂ UL :=
  ((shift μ hμ).comp (Subalgebra.center ℂ UL).val).codRestrict (Subalgebra.center ℂ UL)
    (fun z => shift_mem_center μ hμ z.property)

@[simp]
theorem centerShift_val (hμ : ∀ U V : L, μ ⁅U, V⁆ = 0) (z : Subalgebra.center ℂ UL) :
    (centerShift μ hμ z).val = shift μ hμ z.val :=
  rfl

end Shift

section Intertwining

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- If `ρ(U) T = T (ρ(U) + μ(U))` for every `U`, then `ρ(y) T = T ρ(shift μ y)` for every
element `y` of the enveloping algebra. -/
theorem lift_mul_eq_mul_lift_shift (ρ : L →ₗ⁅ℂ⁆ A) (T : A) (μ : L →ₗ[ℂ] ℂ)
    (hμ : ∀ U V : L, μ ⁅U, V⁆ = 0)
    (hT : ∀ U : L, ρ U * T = T * (ρ U + algebraMap ℂ A (μ U))) (y : UL) :
    UniversalEnvelopingAlgebra.lift ℂ ρ y * T =
      T * UniversalEnvelopingAlgebra.lift ℂ ρ (shift μ hμ y) := by
  have hsurj : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ L) :=
    RingCon.mkₐ_surjective (α := ℂ) (UniversalEnvelopingAlgebra.ringCon ℂ L)
  obtain ⟨t, rfl⟩ := hsurj y
  induction t using TensorAlgebra.induction with
  | algebraMap c =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]
    exact Algebra.commutes c T
  | «ι» U =>
    change UniversalEnvelopingAlgebra.lift ℂ ρ (UniversalEnvelopingAlgebra.ι ℂ U) * T =
      T * UniversalEnvelopingAlgebra.lift ℂ ρ (shift μ hμ (UniversalEnvelopingAlgebra.ι ℂ U))
    rw [shift_ι, map_add, AlgHom.commutes, UniversalEnvelopingAlgebra.lift_ι_apply]
    exact hT U
  | mul x z hx hz =>
    simp only [map_mul]
    rw [mul_assoc, hz, ← mul_assoc, hx, mul_assoc]
  | add x z hx hz =>
    simp only [map_add]
    rw [add_mul, mul_add, hx, hz]

/-- The intertwining relation on generators forces the linear form to vanish on brackets,
provided `T ≠ 0` in a torsion-free algebra. -/
theorem lie_eq_zero_of_intertwining [NoZeroSMulDivisors ℂ A] (ρ : L →ₗ⁅ℂ⁆ A) (T : A)
    (hT0 : T ≠ 0) (μ : L →ₗ[ℂ] ℂ)
    (hT : ∀ U : L, ρ U * T = T * (ρ U + algebraMap ℂ A (μ U))) (U V : L) :
    μ ⁅U, V⁆ = 0 := by
  have hbr : ρ ⁅U, V⁆ = ρ U * ρ V - ρ V * ρ U := by
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
  have key : ρ ⁅U, V⁆ * T = T * (ρ ⁅U, V⁆ + algebraMap ℂ A (μ ⁅U, V⁆)) := hT _
  have hUV : ρ U * ρ V * T =
      T * ((ρ U + algebraMap ℂ A (μ U)) * (ρ V + algebraMap ℂ A (μ V))) := by
    rw [mul_assoc, hT V, ← mul_assoc, hT U, mul_assoc]
  have hVU : ρ V * ρ U * T =
      T * ((ρ V + algebraMap ℂ A (μ V)) * (ρ U + algebraMap ℂ A (μ U))) := by
    rw [mul_assoc, hT U, ← mul_assoc, hT V, mul_assoc]
  have h1 := Algebra.commutes (μ U) (ρ V)
  have h2 := Algebra.commutes (μ V) (ρ U)
  have h3 : algebraMap ℂ A (μ U) * algebraMap ℂ A (μ V) =
      algebraMap ℂ A (μ V) * algebraMap ℂ A (μ U) :=
    ((Commute.all (μ U) (μ V)).map (algebraMap ℂ A)).eq
  have hcomm : ρ ⁅U, V⁆ * T = T * ρ ⁅U, V⁆ := by
    rw [hbr, sub_mul, hUV, hVU, ← mul_sub]
    congr 1
    rw [add_mul, add_mul, mul_add, mul_add, mul_add, mul_add, h1, h2, h3]
    abel
  rw [hcomm, mul_add, left_eq_add, ← Algebra.commutes, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul] at key
  exact (smul_eq_zero.mp key).resolve_right hT0

/-- A nonzero element satisfying the intertwining relation on generators intertwines the
center of the enveloping algebra with itself through an algebra endomorphism of the center. -/
theorem exists_centerShift_intertwining [NoZeroSMulDivisors ℂ A] (ρ : L →ₗ⁅ℂ⁆ A) (T : A)
    (hT0 : T ≠ 0) (μ : L →ₗ[ℂ] ℂ)
    (hT : ∀ U : L, ρ U * T = T * (ρ U + algebraMap ℂ A (μ U))) :
    ∃ θ : Subalgebra.center ℂ UL →ₐ[ℂ] Subalgebra.center ℂ UL,
      ∀ z : Subalgebra.center ℂ UL,
        UniversalEnvelopingAlgebra.lift ℂ ρ z.val * T =
          T * UniversalEnvelopingAlgebra.lift ℂ ρ (θ z).val := by
  have hμ := lie_eq_zero_of_intertwining ρ T hT0 μ hT
  exact ⟨centerShift μ hμ, fun z => lift_mul_eq_mul_lift_shift ρ T μ hμ hT z.val⟩

end Intertwining

end Langlands.Algebra.EnvelopingCharacterShift
