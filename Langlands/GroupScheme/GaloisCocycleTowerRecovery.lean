import Langlands.GroupScheme.GaloisCocycleFiniteRecovery

/-! # Recovery of coefficient cocycles in a general field tower -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.GaloisCocycleTowerRecovery

open GaloisPoint GaloisPointComparison

variable (k E K : Type u) [Field k] [Field E] [Field K]
  [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  (c : (K ≃ₐ[k] K) → G.affinePoints (CommAlgCat.of k K))
  (hc : ∀ σ τ, c (σ * τ) = c σ * conjugate k K G σ (c τ))
  [Normal k E]
  (hE : ∀ σ : K ≃ₐ[k] K, σ.restrictNormal E = 1 → c σ = 1)

include hc hE in
/-- Kernel triviality makes a coefficient cocycle depend only on restriction. -/
theorem value_eq_of_restrict_eq (σ τ : K ≃ₐ[k] K)
    (h : σ.restrictNormal E = τ.restrictNormal E) : c σ = c τ := by
  have hfix : (τ⁻¹ * σ).restrictNormal E = 1 := by
    change (AlgEquiv.restrictNormalHom E) (τ⁻¹ * σ) = 1
    rw [map_mul, map_inv]
    change (τ.restrictNormal E)⁻¹ * σ.restrictNormal E = 1
    rw [h, inv_mul_cancel]
  calc
    c σ = c (τ * (τ⁻¹ * σ)) := by rw [mul_inv_cancel_left]
    _ = c τ := by rw [hc, hE _ hfix, map_one, mul_one]

include hc hE in
/-- Every automorphism in the restriction kernel fixes every coefficient value. -/
theorem conjugate_value (σ τ : K ≃ₐ[k] K) (hτ : τ.restrictNormal E = 1) :
    conjugate k K G τ (c σ) = c σ := by
  have heq : (τ * σ).restrictNormal E = σ.restrictNormal E := by
    change (AlgEquiv.restrictNormalHom E) (τ * σ) = _
    rw [map_mul]
    change τ.restrictNormal E * σ.restrictNormal E = _
    rw [hτ, one_mul]
  have hval := value_eq_of_restrict_eq k E K G c hc hE (τ * σ) σ heq
  rw [hc, hE _ hτ, one_mul] at hval
  exact hval

variable [IsGalois k K] [IsAffine G.X.left]

/-- The cocycle values lie in the actual relative fixed-point subgroup. -/
def fixedValue (σ : K ≃ₐ[k] K) : relativeFixedSubgroup k E K G :=
  ⟨c σ, fun τ => conjugate_value k E K G c hc hE σ (τ.restrictScalars k)
    (restrictNormal_relativeAut k E K τ)⟩

/-- Recover a value over E by descending the value of a chosen lift. -/
def value (σ : E ≃ₐ[k] E) : G.affinePoints (CommAlgCat.of k E) := by
  letI : IsGalois E K := IsGalois.tower_top_of_isGalois k E K
  exact relativeAlgebraicDescend k E K G (fixedValue k E K G c hc hE (σ.liftNormal K))

/-- Extension recovers every original value independently of a choice of lift. -/
theorem extend_value (σ : K ≃ₐ[k] K) :
    relativeExtend k E K G (value k E K G c hc hE (σ.restrictNormal E)) = c σ := by
  let : IsGalois E K := IsGalois.tower_top_of_isGalois k E K
  rw [value, relativeExtend_relativeAlgebraicDescend]
  exact value_eq_of_restrict_eq k E K G c hc hE _ _
    (AlgEquiv.restrict_liftNormal _ _)

/-- The recovered coefficient values satisfy the cocycle law. -/
theorem value_mul (σ τ : E ≃ₐ[k] E) :
    value k E K G c hc hE (σ * τ) =
      value k E K G c hc hE σ *
        conjugate k E G σ (value k E K G c hc hE τ) := by
  let s := σ.liftNormal K
  let t := τ.liftNormal K
  have hs : s.restrictNormal E = σ := AlgEquiv.restrict_liftNormal _ _
  have ht : t.restrictNormal E = τ := AlgEquiv.restrict_liftNormal _ _
  have hst : (s * t).restrictNormal E = σ * τ := by
    change (AlgEquiv.restrictNormalHom E) (s * t) = _
    rw [map_mul]
    exact congrArg₂ (· * ·) hs ht
  apply relativeExtend_injective k E K G
  calc
    relativeExtend k E K G (value k E K G c hc hE (σ * τ)) = c (s * t) := by
      rw [← hst, extend_value]
    _ = c s * conjugate k K G s (c t) := hc s t
    _ = relativeExtend k E K G
        (value k E K G c hc hE σ * conjugate k E G σ (value k E K G c hc hE τ)) := by
      rw [map_mul, ← hs, relativeExtend_conjugate, extend_value, ← ht, extend_value]

end Langlands.GroupScheme.GaloisCocycleTowerRecovery

namespace Langlands.GroupScheme.GaloisCocycleTowerRecovery

open GaloisPoint GaloisPointComparison

variable (k E K : Type u) [Field k] [Field E] [Field K]
  [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  (c : (K ≃ₐ[k] K) → rationalPoints (baseChanged k K G))
  (hc : ∀ σ τ, c (σ * τ) = c σ * rationalConjugate k K G σ (c τ))
  [Normal k E]
  (hE : ∀ σ : K ≃ₐ[k] K, σ.restrictNormal E = 1 → c σ = 1)

include hc in
private theorem rationalCoefficients_mul (σ τ : K ≃ₐ[k] K) :
    baseChangeCoeffEquiv k K G (c (σ * τ)) =
      baseChangeCoeffEquiv k K G (c σ) *
        conjugate k K G σ (baseChangeCoeffEquiv k K G (c τ)) := by
  rw [hc, map_mul, baseChangeCoeffEquiv_rationalConjugate]

include hE in
private theorem rationalCoefficients_trivial (σ : K ≃ₐ[k] K)
    (hσ : σ.restrictNormal E = 1) :
    baseChangeCoeffEquiv k K G (c σ) = 1 := by
  rw [hE σ hσ, map_one]

variable [IsGalois k K] [IsAffine G.X.left]

/-- The recovered cocycle takes values in rational points over the supplied E. -/
def rationalValue (σ : E ≃ₐ[k] E) : rationalPoints (baseChanged k E G) :=
  (baseChangeCoeffEquiv k E G).symm
    (value k E K G (fun τ => baseChangeCoeffEquiv k K G (c τ))
      (rationalCoefficients_mul k K G c hc)
      (rationalCoefficients_trivial k E K G c hE) σ)

/-- Actual rational coefficient extension recovers every original value. -/
theorem relativeRationalExtend_rationalValue (σ : K ≃ₐ[k] K) :
    relativeRationalExtend k E K G
      (rationalValue k E K G c hc hE (σ.restrictNormal E)) = c σ := by
  apply (baseChangeCoeffEquiv k K G).injective
  rw [baseChangeCoeffEquiv_relativeRationalExtend, rationalValue,
    MulEquiv.apply_symm_apply]
  exact extend_value k E K G _ _ _ σ

/-- The recovered rational points satisfy the actual rational cocycle identity. -/
theorem rationalValue_mul (σ τ : E ≃ₐ[k] E) :
    rationalValue k E K G c hc hE (σ * τ) =
      rationalValue k E K G c hc hE σ *
        rationalConjugate k E G σ (rationalValue k E K G c hc hE τ) := by
  apply (baseChangeCoeffEquiv k E G).injective
  simp only [map_mul, baseChangeCoeffEquiv_rationalConjugate, rationalValue,
    MulEquiv.apply_symm_apply]
  exact value_mul k E K G _ _ _ σ τ

include hc hE in
/-- Kernel triviality recovers a rational cocycle on any normal field in a
Galois tower, without requiring a particular intermediate-field carrier. -/
theorem exists_rational_cocycle :
    ∃ d : (E ≃ₐ[k] E) → rationalPoints (baseChanged k E G),
      (∀ σ τ, d (σ * τ) = d σ * rationalConjugate k E G σ (d τ)) ∧
      ∀ σ : K ≃ₐ[k] K,
        relativeRationalExtend k E K G (d (σ.restrictNormal E)) = c σ :=
  ⟨rationalValue k E K G c hc hE, rationalValue_mul k E K G c hc hE,
    relativeRationalExtend_rationalValue k E K G c hc hE⟩

end Langlands.GroupScheme.GaloisCocycleTowerRecovery
