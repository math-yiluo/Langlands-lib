import Langlands.Geometry.Building.RationalRootForms
import Langlands.Geometry.Building.AffineDerivativeRootPairing

/-! # Full derivative root pairings on the actual relative-root span -/

noncomputable section

universe u uA

open CategoryTheory AlgebraicGeometry Module
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AffineRootSystem

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp)
  {A : Type uA} [AddTorsor (TranslationSpace i) A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ)
  (hderiv : derivativeRoots Ψ = Set.range (rootForm i))

/-- Identify the actual rational relative-root span with the full derivative-root span. -/
def relativeDerivativeRootEquiv :
    relativeRootSpan i ≃ₗ[ℚ] hΨ.derivativeRootSpanRat :=
  (relativeRootFormEquiv i hS).trans (LinearEquiv.ofEq _ _ (by
    rw [hΨ.derivativeRootSpanRat_eq, hderiv]))

@[simp] theorem relativeDerivativeRootEquiv_coe (x : relativeRootSpan i) :
    (relativeDerivativeRootEquiv i hS hΨ hderiv x :
      Module.Dual ℝ (TranslationSpace i)) = relativeRootForm i x := rfl

/-- Transport the full derivative root system to the actual relative-root span,
with the rational dual as coroot space. -/
def relativeDerivativePairing :
    RootPairing (derivativeRoots Ψ) ℚ (relativeRootSpan i)
      (Module.Dual ℚ (relativeRootSpan i)) :=
  hΨ.rationalDerivativePairing.map (Equiv.refl _)
    (relativeDerivativeRootEquiv i hS hΨ hderiv).symm
    (relativeDerivativeRootEquiv i hS hΨ hderiv).dualMap

instance relativeDerivativePairing_isRootSystem :
    (relativeDerivativePairing i hS hΨ hderiv).IsRootSystem := by
  unfold relativeDerivativePairing
  infer_instance

theorem relativeDerivativePairing_toLinearMap :
    (relativeDerivativePairing i hS hΨ hderiv).toLinearMap =
      Module.Dual.eval ℚ (relativeRootSpan i) := by
  ext x y
  change hΨ.rationalDerivativePairing.toLinearMap
    (relativeDerivativeRootEquiv i hS hΨ hderiv x)
    ((relativeDerivativeRootEquiv i hS hΨ hderiv).dualMap.symm y) = y x
  rw [hΨ.rationalDerivativePairing_toLinearMap]
  simp

@[simp] theorem relativeDerivativePairing_pairing (a b : derivativeRoots Ψ) :
    (relativeDerivativePairing i hS hΨ hderiv).pairing a b =
      hΨ.rationalDerivativePairing.pairing a b := by
  change hΨ.rationalDerivativePairing.toLinearMap
    ((relativeDerivativeRootEquiv i hS hΨ hderiv)
      ((relativeDerivativeRootEquiv i hS hΨ hderiv).symm
        (hΨ.rationalDerivativePairing.root a)))
    ((relativeDerivativeRootEquiv i hS hΨ hderiv).dualMap.symm
      ((relativeDerivativeRootEquiv i hS hΨ hderiv).dualMap
        (hΨ.rationalDerivativePairing.coroot b))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  rfl

instance relativeDerivativePairing_isCrystallographic :
    (relativeDerivativePairing i hS hΨ hderiv).IsCrystallographic where
  exists_value a b := by
    obtain ⟨n, hn⟩ := hΨ.rationalDerivativePairing.exists_value (S := ℤ) a b
    exact ⟨n, by simpa only [relativeDerivativePairing_pairing] using hn⟩

@[simp] theorem relativeRootForm_relativeDerivativePairing_root
    (a : derivativeRoots Ψ) :
    relativeRootForm i ((relativeDerivativePairing i hS hΨ hderiv).root a) = a.val := by
  change relativeRootForm i
    ((relativeDerivativeRootEquiv i hS hΨ hderiv).symm
      (hΨ.rationalDerivativePairing.root a)) = a.val
  have h := relativeDerivativeRootEquiv_coe i hS hΨ hderiv
    ((relativeDerivativeRootEquiv i hS hΨ hderiv).symm
      (hΨ.rationalDerivativePairing.root a))
  simpa only [LinearEquiv.apply_symm_apply,
    IsAffineRootSystemWithRankZero.rationalDerivativePairing_coe_root] using h.symm

theorem relativeDerivativePairing_root_image :
    Subtype.val '' Set.range (relativeDerivativePairing i hS hΨ hderiv).root =
      toRat '' relativeRoots i := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    obtain ⟨χ, hχ⟩ : ∃ χ : relativeRoots i, rootForm i χ = a.val := by
      have ha : a.val ∈ Set.range (rootForm i) := by
        rw [← hderiv]
        exact a.property
      exact ha
    have hx : (relativeDerivativePairing i hS hΨ hderiv).root a =
        ⟨toRat χ.val, toRat_mem_ratSpan χ.property⟩ := by
      apply relativeRootForm_injective i hS
      rw [relativeRootForm_relativeDerivativePairing_root, relativeRootForm_toRat, hχ]
    exact ⟨χ.val, χ.property, congrArg Subtype.val hx.symm⟩
  · rintro ⟨χ, hχ, rfl⟩
    let a : derivativeRoots Ψ := ⟨rootForm i ⟨χ, hχ⟩, hderiv.symm ▸ ⟨⟨χ, hχ⟩, rfl⟩⟩
    have hx : (relativeDerivativePairing i hS hΨ hderiv).root a =
        ⟨toRat χ, toRat_mem_ratSpan hχ⟩ := by
      apply relativeRootForm_injective i hS
      rw [relativeRootForm_relativeDerivativePairing_root]
      exact (relativeRootForm_toRat i ⟨χ, hχ⟩).symm
    exact ⟨_, ⟨a, rfl⟩, congrArg Subtype.val hx⟩

end Langlands.Geometry.Building
