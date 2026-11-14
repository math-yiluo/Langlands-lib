import Langlands.GroupScheme.AlgebraicGaloisPointDescent
import Langlands.GroupScheme.GaloisPointRationalTower
import Mathlib.FieldTheory.Normal.Closure

/-! # Finite recovery of coefficient Galois cocycles -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace GaloisPoint

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

private instance recoveryBaseChanged_isAffine :
    IsAffine (GaloisPointComparison.baseChanged k L G).X.left := by
  change IsAffine (pullback G.X.hom (GaloisPointComparison.baseMap k L))
  infer_instance

open GaloisPointComparison

variable [IsGalois L M]

/-- Relative fixed points descend over an arbitrary Galois extension. -/
def relativeAlgebraicDescend (x : relativeFixedSubgroup k L M G) :
    G.affinePoints (CommAlgCat.of k L) :=
  coefficientBaseChangeEquiv k L L G
    (algebraicDescend L M (baseChanged k L G)
      ⟨(coefficientBaseChangeEquiv k L M G).symm x.val, fun σ => by
        apply (coefficientBaseChangeEquiv k L M G).injective
        rw [coefficientBaseChangeEquiv_conjugate, MulEquiv.apply_symm_apply]
        exact x.property σ⟩)

@[simp] theorem relativeExtend_relativeAlgebraicDescend
    (x : relativeFixedSubgroup k L M G) :
    relativeExtend k L M G (relativeAlgebraicDescend k L M G x) = x.val := by
  rw [relativeAlgebraicDescend, ← coefficientBaseChangeEquiv_extend,
    extend_algebraicDescend, MulEquiv.apply_symm_apply]

end GaloisPoint

namespace GaloisPointComparison

open GaloisPoint

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Coefficient extension between rational points of two actual base changes. -/
def relativeRationalExtend :
    rationalPoints (baseChanged k L G) →* rationalPoints (baseChanged k M G) :=
  (baseChangeCoeffEquiv k M G).symm.toMonoidHom.comp
    ((relativeExtend k L M G).comp (baseChangeCoeffEquiv k L G).toMonoidHom)

@[simp] theorem baseChangeCoeffEquiv_relativeRationalExtend
    (x : rationalPoints (baseChanged k L G)) :
    baseChangeCoeffEquiv k M G (relativeRationalExtend k L M G x) =
      relativeExtend k L M G (baseChangeCoeffEquiv k L G x) :=
  (baseChangeCoeffEquiv k M G).apply_symm_apply _

/-- On scheme morphisms, relative extension composes the original coefficient
point with the field-inclusion spectrum map. -/
theorem relativeRationalExtend_fst
    (x : rationalPoints (baseChanged k L G)) :
    (relativeRationalExtend k L M G x).left ≫ pullback.fst G.X.hom (baseMap k M) =
      baseMap L M ≫ (x.left ≫ pullback.fst G.X.hom (baseMap k L)) := by
  have h := congrArg (fun p => p.left)
    (baseChangeCoeffEquiv_relativeRationalExtend k L M G x)
  rw [baseChangeCoeffEquiv_left] at h
  change _ = baseMap L M ≫ (baseChangeCoeffEquiv k L G x).left at h
  rwa [baseChangeCoeffEquiv_left] at h

variable [IsAffine G.X.left]

theorem relativeRationalExtend_injective :
    Function.Injective (relativeRationalExtend k L M G) := by
  intro x y h
  apply (baseChangeCoeffEquiv k L G).injective
  apply relativeExtend_injective k L M G
  simpa only [baseChangeCoeffEquiv_relativeRationalExtend] using
    congrArg (baseChangeCoeffEquiv k M G) h

variable [Normal k L]

/-- Restriction of automorphisms commutes with the actual rational extension. -/
theorem relativeRationalExtend_rationalConjugate (σ : M ≃ₐ[k] M)
    (x : rationalPoints (baseChanged k L G)) :
    relativeRationalExtend k L M G (rationalConjugate k L G (σ.restrictNormal L) x) =
      rationalConjugate k M G σ (relativeRationalExtend k L M G x) := by
  apply (baseChangeCoeffEquiv k M G).injective
  simp only [baseChangeCoeffEquiv_relativeRationalExtend,
    baseChangeCoeffEquiv_rationalConjugate]
  exact relativeExtend_conjugate k L M G σ _

end GaloisPointComparison

namespace GaloisCocycleFiniteRecovery

open GaloisPoint GaloisPointComparison

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  (c : (K ≃ₐ[k] K) → G.affinePoints (CommAlgCat.of k K))
  (hc : ∀ σ τ, c (σ * τ) = c σ * conjugate k K G σ (c τ))
  (E : IntermediateField k K) [Normal k E]
  (hE : ∀ σ ∈ E.fixingSubgroup, c σ = 1)

include hc hE in
/-- A cocycle trivial on the fixing subgroup depends only on restriction. -/
theorem value_eq_of_restrict_eq (σ τ : K ≃ₐ[k] K)
    (h : σ.restrictNormal E = τ.restrictNormal E) : c σ = c τ := by
  have hfix : τ⁻¹ * σ ∈ E.fixingSubgroup := by
    rw [← E.restrictNormalHom_ker]
    change (AlgEquiv.restrictNormalHom E) (τ⁻¹ * σ) = 1
    rw [map_mul, map_inv]
    change (τ.restrictNormal E)⁻¹ * σ.restrictNormal E = 1
    rw [h, inv_mul_cancel]
  calc
    c σ = c (τ * (τ⁻¹ * σ)) := by rw [mul_inv_cancel_left]
    _ = c τ := by rw [hc, hE _ hfix, map_one, mul_one]

include hc hE in
/-- The same fixing subgroup fixes every cocycle value coefficientwise. -/
theorem conjugate_value (σ τ : K ≃ₐ[k] K) (hτ : τ ∈ E.fixingSubgroup) :
    conjugate k K G τ (c σ) = c σ := by
  have hτ' : τ.restrictNormal E = 1 := by
    change τ ∈ (AlgEquiv.restrictNormalHom E).ker
    rwa [E.restrictNormalHom_ker]
  have heq : (τ * σ).restrictNormal E = σ.restrictNormal E := by
    change (AlgEquiv.restrictNormalHom E) (τ * σ) = _
    rw [map_mul]
    change τ.restrictNormal E * σ.restrictNormal E = _
    rw [hτ', one_mul]
  have hval := value_eq_of_restrict_eq G c hc E hE (τ * σ) σ heq
  rw [hc, hE _ hτ, one_mul] at hval
  exact hval

variable [IsGalois k K] [IsAffine G.X.left]

/-- Every value is fixed under the relative Galois group. -/
def fixedValue (σ : K ≃ₐ[k] K) : relativeFixedSubgroup k E K G :=
  ⟨c σ, fun τ => conjugate_value G c hc E hE σ (τ.restrictScalars k)
    ((E.fixingSubgroupEquiv).symm τ).property⟩

/-- The finite-level value obtained from any chosen lift of an automorphism. -/
def value (σ : E ≃ₐ[k] E) : G.affinePoints (CommAlgCat.of k E) :=
  relativeAlgebraicDescend k E K G (fixedValue G c hc E hE (σ.liftNormal K))

/-- Extending the recovered value gives the original cocycle value exactly. -/
theorem extend_value (σ : K ≃ₐ[k] K) :
    relativeExtend k E K G (value G c hc E hE (σ.restrictNormal E)) = c σ := by
  rw [value, relativeExtend_relativeAlgebraicDescend]
  exact value_eq_of_restrict_eq G c hc E hE _ _
    (AlgEquiv.restrict_liftNormal _ _)

/-- The recovered values satisfy the coefficient cocycle identity. -/
theorem value_mul (σ τ : E ≃ₐ[k] E) :
    value G c hc E hE (σ * τ) =
      value G c hc E hE σ *
        conjugate k E G σ (value G c hc E hE τ) := by
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
    relativeExtend k E K G (value G c hc E hE (σ * τ)) = c (s * t) := by
      rw [← hst, extend_value]
    _ = c s * conjugate k K G s (c t) := hc s t
    _ = relativeExtend k E K G
        (value G c hc E hE σ * conjugate k E G σ (value G c hc E hE τ)) := by
      rw [map_mul, ← hs, relativeExtend_conjugate, extend_value, ← ht, extend_value]

end GaloisCocycleFiniteRecovery

namespace GaloisCocycleFiniteRecovery

open GaloisPoint GaloisPointComparison

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  (c : (K ≃ₐ[k] K) → rationalPoints (baseChanged k K G))
  (hc : ∀ σ τ, c (σ * τ) = c σ * rationalConjugate k K G σ (c τ))
  (E : IntermediateField k K) [Normal k E]
  (hE : ∀ σ ∈ E.fixingSubgroup, c σ = 1)

include hc in
private theorem rationalCoefficients_mul (σ τ : K ≃ₐ[k] K) :
    baseChangeCoeffEquiv k K G (c (σ * τ)) =
      baseChangeCoeffEquiv k K G (c σ) *
        conjugate k K G σ (baseChangeCoeffEquiv k K G (c τ)) := by
  rw [hc, map_mul, baseChangeCoeffEquiv_rationalConjugate]

omit [Normal k E] in
include hE in
private theorem rationalCoefficients_trivial (σ : K ≃ₐ[k] K)
    (hσ : σ ∈ E.fixingSubgroup) :
    baseChangeCoeffEquiv k K G (c σ) = 1 := by
  rw [hE σ hσ, map_one]

variable [IsGalois k K] [IsAffine G.X.left]

/-- The recovered cocycle on the rational points of the actual finite base change. -/
def rationalValue (σ : E ≃ₐ[k] E) : rationalPoints (baseChanged k E G) :=
  (baseChangeCoeffEquiv k E G).symm
    (value G (fun τ => baseChangeCoeffEquiv k K G (c τ))
      (rationalCoefficients_mul G c hc) E (rationalCoefficients_trivial G c E hE) σ)

/-- Extension recovers every original rational-point value, for every lift. -/
theorem relativeRationalExtend_rationalValue (σ : K ≃ₐ[k] K) :
    relativeRationalExtend k E K G (rationalValue G c hc E hE (σ.restrictNormal E)) =
      c σ := by
  apply (baseChangeCoeffEquiv k K G).injective
  rw [baseChangeCoeffEquiv_relativeRationalExtend, rationalValue,
    MulEquiv.apply_symm_apply]
  exact extend_value G _ _ E _ σ

/-- The recovered rational-point values satisfy the actual coefficient cocycle law. -/
theorem rationalValue_mul (σ τ : E ≃ₐ[k] E) :
    rationalValue G c hc E hE (σ * τ) =
      rationalValue G c hc E hE σ *
        rationalConjugate k E G σ (rationalValue G c hc E hE τ) := by
  apply (baseChangeCoeffEquiv k E G).injective
  simp only [map_mul, baseChangeCoeffEquiv_rationalConjugate, rationalValue,
    MulEquiv.apply_symm_apply]
  exact value_mul G _ _ E _ σ τ

end GaloisCocycleFiniteRecovery

namespace GaloisCocycleFiniteRecovery

open GaloisPointComparison

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]

/-- A finite field on whose fixing subgroup a function is trivial can be enlarged
to a finite Galois field with the same property. -/
theorem exists_finite_galois_trivial {A : Type*} [One A]
    (c : (K ≃ₐ[k] K) → A)
    (h : ∃ E : IntermediateField k K, FiniteDimensional k E ∧
      ∀ σ ∈ E.fixingSubgroup, c σ = 1) :
    ∃ E : IntermediateField k K, FiniteDimensional k E ∧ IsGalois k E ∧
      ∀ σ ∈ E.fixingSubgroup, c σ = 1 := by
  obtain ⟨E₀, hfin, htriv⟩ := h
  let := hfin
  let E := IntermediateField.normalClosure k E₀ K
  refine ⟨E, inferInstance, inferInstance, fun σ hσ => ?_⟩
  exact htriv σ (IntermediateField.fixingSubgroup_le
    (IntermediateField.le_normalClosure E₀) hσ)

/-- The exact finite-level triviality premise produces a genuine finite Galois
rational-point cocycle, together with recovery of every original value. -/
theorem exists_finite_rational_cocycle
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
    (c : (K ≃ₐ[k] K) → rationalPoints (baseChanged k K G))
    (hc : ∀ σ τ, c (σ * τ) = c σ * rationalConjugate k K G σ (c τ))
    (h : ∃ E : IntermediateField k K, FiniteDimensional k E ∧
      ∀ σ ∈ E.fixingSubgroup, c σ = 1) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E) (hgal : IsGalois k E),
      letI := hgal
      ∃ d : (E ≃ₐ[k] E) → rationalPoints (baseChanged k E G),
        (∀ σ τ, d (σ * τ) = d σ * rationalConjugate k E G σ (d τ)) ∧
        ∀ σ : K ≃ₐ[k] K, relativeRationalExtend k E K G (d (σ.restrictNormal E)) =
          c σ := by
  obtain ⟨E, hfin, hgal, htriv⟩ := exists_finite_galois_trivial c h
  let := hgal
  exact ⟨E, hfin, hgal, rationalValue G c hc E htriv,
    rationalValue_mul G c hc E htriv, relativeRationalExtend_rationalValue G c hc E htriv⟩

end GaloisCocycleFiniteRecovery
end Langlands.GroupScheme
