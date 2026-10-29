import Langlands.Shimura.PEL.IntegralOrder
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # Integer-valued forms on preserved rational lattices -/

noncomputable section

open scoped Pointwise

namespace Langlands.Shimura.PEL

section Pairings

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

omit [Module ℚ V] in
private theorem isInteger_bilinear_of_span
    (B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ) {s t : Set V}
    (h : ∀ x ∈ s, ∀ y ∈ t, IsLocalization.IsInteger ℤ (B x y))
    {x y : V} (hx : x ∈ Submodule.span ℤ s) (hy : y ∈ Submodule.span ℤ t) :
    IsLocalization.IsInteger ℤ (B x y) := by
  have hi : ∀ y ∈ Submodule.span ℤ t, IsLocalization.IsInteger ℤ (B x y) := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact h x hx y hy
      | zero => simpa using (IsLocalization.isInteger_zero (R := ℤ) (S := ℚ))
      | add y z _ _ hy hz =>
        simpa only [map_add] using IsLocalization.isInteger_add hy hz
      | smul n y _ hy =>
        simpa only [map_smul] using IsLocalization.isInteger_smul (a := n) hy
    | zero =>
      intro y _
      simpa using (IsLocalization.isInteger_zero (R := ℤ) (S := ℚ))
    | add x z _ _ hx hz =>
      intro y hy
      simpa only [LinearMap.map_add₂] using
        IsLocalization.isInteger_add (hx y hy) (hz y hy)
    | smul n x _ hx =>
      intro y hy
      simpa only [LinearMap.map_smul₂] using
        IsLocalization.isInteger_smul (a := n) (hx y hy)
  exact hi y hy

/-- One integer clears every pairing value on a finitely generated integer submodule. -/
theorem exists_pairing_denominator (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V) (hL : L.FG) :
    ∃ m : ℤ, m ≠ 0 ∧
      ∀ x ∈ L, ∀ y ∈ L, IsLocalization.IsInteger ℤ (m • B x y) := by
  classical
  obtain ⟨s, hs⟩ := hL
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ)
    (s ×ˢ s) (fun p : V × V => B p.1 p.2)
  refine ⟨m, mem_nonZeroDivisors_iff_ne_zero.mp m.prop, ?_⟩
  intro x hx y hy
  exact isInteger_bilinear_of_span
    ((m : ℤ) • B.restrictScalars₁₂ ℤ ℤ)
    (fun x hx y hy => hm (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩))
    (hs.symm ▸ hx) (hs.symm ▸ hy)

/-- A chosen nonzero common denominator of the rational Gram entries. -/
def pairingDenominator (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V) [Submodule.IsLattice ℚ L] : ℤ :=
  (exists_pairing_denominator B L (Submodule.IsLattice.fg (A := ℚ))).choose

theorem pairingDenominator_ne_zero (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V) [Submodule.IsLattice ℚ L] :
    pairingDenominator B L ≠ 0 :=
  (exists_pairing_denominator B L (Submodule.IsLattice.fg (A := ℚ))).choose_spec.1

theorem pairingDenominator_isInteger (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V) [Submodule.IsLattice ℚ L]
    {x y : V} (hx : x ∈ L) (hy : y ∈ L) :
    IsLocalization.IsInteger ℤ (pairingDenominator B L • B x y) :=
  (exists_pairing_denominator B L (Submodule.IsLattice.fg (A := ℚ))).choose_spec.2
    x hx y hy

/-- View the integer denominator as a nonzero rational scalar. -/
def pairingDenominatorUnit (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V) [Submodule.IsLattice ℚ L] : ℚˣ :=
  Units.mk0 (pairingDenominator B L : ℚ)
    (by exact_mod_cast pairingDenominator_ne_zero B L)

/-- Scale the given lattice, keeping the original rational bilinear form. -/
def integralPairingLattice (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V) [Submodule.IsLattice ℚ L] : Submodule ℤ V :=
  pairingDenominatorUnit B L • L

instance integralPairingLattice_isLattice (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V) [Submodule.IsLattice ℚ L] :
    Submodule.IsLattice ℚ (integralPairingLattice B L) :=
  Submodule.IsLattice.smul ℚ L (pairingDenominatorUnit B L)

/-- Every element of the scaled lattice is an integer multiple of an original element. -/
theorem mem_integralPairingLattice (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V) [Submodule.IsLattice ℚ L] (x : V) :
    x ∈ integralPairingLattice B L ↔
      ∃ y ∈ L, pairingDenominator B L • y = x := by
  change x ∈ (pairingDenominatorUnit B L : ℚ) • L ↔ _
  rw [Submodule.mem_smul_pointwise_iff_exists x (pairingDenominatorUnit B L : ℚ) L]
  simp only [pairingDenominatorUnit, Units.val_mk0, Int.cast_smul_eq_zsmul]

/-- The unchanged rational form has integer values on the scaled lattice. -/
theorem integralPairingLattice_isInteger (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V) [Submodule.IsLattice ℚ L]
    (x y : integralPairingLattice B L) :
    IsLocalization.IsInteger ℤ (B (x : V) (y : V)) := by
  obtain ⟨a, ha, hax⟩ := (mem_integralPairingLattice B L x).mp x.prop
  obtain ⟨b, hb, hby⟩ := (mem_integralPairingLattice B L y).mp y.prop
  rw [← hax, ← hby, B.map_smul_of_tower, LinearMap.smul_apply,
    (B a).map_smul_of_tower, smul_comm]
  exact IsLocalization.isInteger_smul (a := pairingDenominator B L)
    (pairingDenominator_isInteger B L ha hb)

/-- Restrict a rational form to an integer lattice and its values to the integers. -/
def integerPairing (B : LinearMap.BilinForm ℚ V) (L : Submodule ℤ V)
    (h : ∀ x y : L, IsLocalization.IsInteger ℤ (B (x : V) (y : V))) :
    LinearMap.BilinForm ℤ L :=
  LinearMap.restrictScalarsRange₂ L.subtype L.subtype
    (Algebra.linearMap ℤ ℚ) (by
      intro a b hab
      exact Int.cast_injective (α := ℚ) hab)
    B h

@[simp] theorem integerPairing_cast (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V)
    (h : ∀ x y : L, IsLocalization.IsInteger ℤ (B (x : V) (y : V))) (x y : L) :
    (integerPairing B L h x y : ℚ) = B (x : V) (y : V) :=
  by
    simpa [integerPairing] using
      LinearMap.restrictScalarsRange₂_apply L.subtype L.subtype
        (Algebra.linearMap ℤ ℚ) _ B h x y

theorem integerPairing_isAlt (B : LinearMap.BilinForm ℚ V) (L : Submodule ℤ V)
    (h : ∀ x y : L, IsLocalization.IsInteger ℤ (B (x : V) (y : V)))
    (hB : B.IsAlt) : (integerPairing B L h).IsAlt := by
  intro x
  apply Int.cast_injective (α := ℚ)
  simpa only [integerPairing_cast, Int.cast_zero] using hB (x : V)

/-- Restriction to a full lattice retains both separating properties. -/
theorem integerPairing_nondegenerate (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V)
    (h : ∀ x y : L, IsLocalization.IsInteger ℤ (B (x : V) (y : V)))
    (hfull : Submodule.span ℚ (L : Set V) = ⊤)
    (hB : B.Nondegenerate) : (integerPairing B L h).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    apply hB.1
    have he : B (x : V) = 0 := LinearMap.ext_on hfull (by
      intro y hy
      simpa only [integerPairing_cast, Int.cast_zero, LinearMap.zero_apply] using
        congrArg (fun z : ℤ => (z : ℚ)) (hx ⟨y, hy⟩))
    intro y
    exact LinearMap.congr_fun he y
  · intro y hy
    apply Subtype.ext
    apply hB.2
    have he : B.flip (y : V) = 0 := LinearMap.ext_on hfull (by
      intro x hx
      change B x (y : V) = 0
      simpa only [integerPairing_cast, Int.cast_zero] using
        congrArg (fun z : ℤ => (z : ℚ)) (hy ⟨x, hx⟩))
    intro x
    exact LinearMap.congr_fun he x

end Pairings

section Actions

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- A left multiplier preserving the original lattice also preserves its integer scaling. -/
theorem latticeStabilizer_le_integralPairingLatticeStabilizer
    (B : LinearMap.BilinForm ℚ A) (L : Submodule ℤ A) [Submodule.IsLattice ℚ L] :
    latticeStabilizer L ≤ latticeStabilizer (integralPairingLattice B L) := by
  intro a ha x hx
  obtain ⟨y, hy, rfl⟩ := (mem_integralPairingLattice B L x).mp hx
  rw [mul_smul_comm]
  exact (mem_integralPairingLattice B L _).mpr ⟨a * y, ha y hy, rfl⟩

/-- The original lattice stabilizer acts on the lattice with integer pairing. -/
def integralPairingLatticeAction (B : LinearMap.BilinForm ℚ A)
    (L : Submodule ℤ A) [Submodule.IsLattice ℚ L] :
    latticeStabilizer L →+* Module.End ℤ (integralPairingLattice B L) :=
  (latticeStabilizerAction (integralPairingLattice B L)).comp
    (Subalgebra.inclusion (latticeStabilizer_le_integralPairingLatticeStabilizer B L)).toRingHom

@[simp] theorem integralPairingLatticeAction_apply (B : LinearMap.BilinForm ℚ A)
    (L : Submodule ℤ A) [Submodule.IsLattice ℚ L]
    (a : latticeStabilizer L) (x : integralPairingLattice B L) :
    (integralPairingLatticeAction B L a x : A) = (a : A) * x := rfl

/-- Full rational span makes the scaled left multiplication action faithful. -/
theorem integralPairingLatticeAction_injective (B : LinearMap.BilinForm ℚ A)
    (L : Submodule ℤ A) [Submodule.IsLattice ℚ L] :
    Function.Injective (integralPairingLatticeAction B L) := by
  intro a b h
  apply Subtype.ext
  have he : LinearMap.mulLeft ℚ (a : A) = LinearMap.mulLeft ℚ (b : A) :=
    LinearMap.ext_on
      (Submodule.IsLattice.span_eq_top (A := ℚ) (M := integralPairingLattice B L)) (by
        intro x hx
        exact congrArg
          (fun f : Module.End ℤ (integralPairingLattice B L) => (f ⟨x, hx⟩ : A)) h)
  simpa only [LinearMap.mulLeft_apply, mul_one] using LinearMap.congr_fun he 1

end Actions

end Langlands.Shimura.PEL
