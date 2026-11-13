import Langlands.Geometry.Building.SpecialPointExistence
import Mathlib.LinearAlgebra.RootSystem.BaseChange
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-! # Rational root systems from all derivatives of affine roots -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

open Set Module

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)

instance derivativePairing_isRootSystem : hΨ.derivativePairing.IsRootSystem := by
  let := hΨ.finite_derivativeRoots.fintype
  have hrange : range hΨ.derivativePairing.root = derivativeRoots Ψ := by
    ext
    simp
  have hspan : hΨ.derivativePairing.rootSpan ℝ = ⊤ := by
    change Submodule.span ℝ (range hΨ.derivativePairing.root) = ⊤
    rw [hrange]
    exact hΨ.span_derivativeRoots_eq_top
  exact ⟨hspan, hΨ.derivativePairing.rootSpan_eq_top_iff.mp hspan⟩

/-- The rational span of all derivative roots. -/
abbrev derivativeRootSpanRat := hΨ.derivativePairing.rootSpan ℚ

theorem derivativeRootSpanRat_eq :
    hΨ.derivativeRootSpanRat = Submodule.span ℚ (derivativeRoots Ψ) := by
  change Submodule.span ℚ (range hΨ.derivativePairing.root) = _
  congr 1
  ext
  simp

/-- The restriction of the full derivative pairing to rational root and coroot spans. -/
abbrev derivativePairingRat :=
  hΨ.derivativePairing.restrictScalarsRat

/-- The full rational derivative root pairing, with coroots in the dual root space
and the evaluation pairing. -/
def rationalDerivativePairing :
    RootPairing (derivativeRoots Ψ) ℚ hΨ.derivativeRootSpanRat
      (Module.Dual ℚ hΨ.derivativeRootSpanRat) :=
  hΨ.derivativePairingRat.map (Equiv.refl _) (LinearEquiv.refl _ _)
    hΨ.derivativePairingRat.toLinearMap.flip.toPerfPair

instance rationalDerivativePairing_isRootSystem :
    hΨ.rationalDerivativePairing.IsRootSystem := by
  unfold rationalDerivativePairing
  infer_instance

theorem rationalDerivativePairing_toLinearMap :
    hΨ.rationalDerivativePairing.toLinearMap =
      Module.Dual.eval ℚ hΨ.derivativeRootSpanRat := by
  ext x y
  change hΨ.derivativePairingRat.toLinearMap x
    (hΨ.derivativePairingRat.toLinearMap.flip.toPerfPair.symm y) = y x
  exact hΨ.derivativePairingRat.toLinearMap.apply_toPerfPair_flip y x

@[simp] theorem rationalDerivativePairing_coe_root (a : derivativeRoots Ψ) :
    (hΨ.rationalDerivativePairing.root a : Module.Dual ℝ V) = a.val := rfl

theorem rationalDerivativePairing_root_image :
    Subtype.val '' range hΨ.rationalDerivativePairing.root = derivativeRoots Ψ := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact a.property
  · intro hx
    exact ⟨_, ⟨⟨x, hx⟩, rfl⟩, hΨ.rationalDerivativePairing_coe_root ⟨x, hx⟩⟩

@[simp] theorem rationalDerivativePairing_pairing (a b : derivativeRoots Ψ) :
    algebraMap ℚ ℝ (hΨ.rationalDerivativePairing.pairing a b) =
      a.val (hΨ.derivativeCoroot b) := by
  have hmap : hΨ.rationalDerivativePairing.pairing a b =
      hΨ.derivativePairingRat.pairing a b := by
    change hΨ.derivativePairingRat.toLinearMap (hΨ.derivativePairingRat.root a)
      (hΨ.derivativePairingRat.toLinearMap.flip.toPerfPair.symm
        (hΨ.derivativePairingRat.toLinearMap.flip.toPerfPair
          (hΨ.derivativePairingRat.coroot b))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [hmap]
  let : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)
  exact hΨ.derivativePairing.restrictScalars_pairing ℚ a b

instance rationalDerivativePairing_isCrystallographic :
    hΨ.rationalDerivativePairing.IsCrystallographic where
  exists_value a b := by
    obtain ⟨n, hn⟩ := hΨ.derivativePairing.exists_value (S := ℤ) a b
    refine ⟨n, ?_⟩
    change (n : ℚ) = hΨ.rationalDerivativePairing.pairing a b
    change (n : ℝ) = a.val (hΨ.derivativeCoroot b) at hn
    apply FaithfulSMul.algebraMap_injective ℚ ℝ
    simpa only [map_intCast, rationalDerivativePairing_pairing] using hn

theorem rationalDerivativePairing_pairing_symmetric_iff :
    (∀ a b, hΨ.rationalDerivativePairing.pairing a b =
      hΨ.rationalDerivativePairing.pairing b a) ↔
    ∀ a b : derivativeRoots Ψ,
      a.val (hΨ.derivativeCoroot b) = b.val (hΨ.derivativeCoroot a) := by
  constructor
  · intro h a b
    simpa only [rationalDerivativePairing_pairing] using congrArg (algebraMap ℚ ℝ) (h a b)
  · intro h a b
    apply FaithfulSMul.algebraMap_injective ℚ ℝ
    simpa only [rationalDerivativePairing_pairing] using h a b

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
