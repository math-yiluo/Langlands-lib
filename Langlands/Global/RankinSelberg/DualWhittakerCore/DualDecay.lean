import Langlands.Global.RankinSelberg.WhittakerExpansionCore.ExpansionRealization
import Langlands.Global.RankinSelberg.UnequalAnalyticPoints

/-! # Whittaker decay classes are stable under transpose inverse

For a space `V` of functions on `GL_{r+1}(𝔸)` with archimedean right derivatives `R`, let
`iotaSpace V` be the space of the functions `f ∘ ι`, `f ∈ V`, where `ι(g) = ᵗg⁻¹`. Its
derivatives are `iotaDerivative R Z = (· ∘ ι) ∘ R(-ᵗZ) ∘ (· ∘ ι)⁻¹`. If `(V, R)` is a
`WhittakerDecayClass`, then so is `(iotaSpace V, iotaDerivative R)`
(`whittakerDecayClass_iotaSpace`).

The point-level facts behind this are `ι(x · finitePoint l) = ι(x) · finitePoint(ᵗl⁻¹)`,
`ι(archPoint Z) = archPoint(-ᵗZ)` (because `ᵗ(1 + Z)⁻¹ = 1 - ᵗZ` when `Z² = 0`), and
`|det ι(x)| = |det x|⁻¹`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints UnequalAnalytic

local instance dualDecaySchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualDecaySchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

section Points

variable {n : ℕ}

theorem infinite_inverseTranspose (g : AdelicGL F n) :
    AdelicGL.infinite F n (GeneralLinear.inverseTranspose n (Adeles F) g) =
      GeneralLinear.inverseTranspose n _ (AdelicGL.infinite F n g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [AdelicGL.infinite_apply, GeneralLinear.inverseTranspose_entry,
    GeneralLinear.inverseTranspose_entry, ← map_inv, AdelicGL.infinite_apply]

theorem finite_inverseTranspose (g : AdelicGL F n) :
    AdelicGL.finite F n (GeneralLinear.inverseTranspose n (Adeles F) g) =
      GeneralLinear.inverseTranspose n _ (AdelicGL.finite F n g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [AdelicGL.finite_apply, GeneralLinear.inverseTranspose_entry,
    GeneralLinear.inverseTranspose_entry, ← map_inv, AdelicGL.finite_apply]

theorem inverseTranspose_ofFinite (l : FiniteAdelicGL F n) :
    GeneralLinear.inverseTranspose n (Adeles F) (AdelicGL.ofFinite F n l) =
      AdelicGL.ofFinite F n (GeneralLinear.inverseTranspose n _ l) := by
  refine AdelicGL.ext_infinite_finite F n ?_ ?_
  · rw [infinite_inverseTranspose, AdelicGL.infinite_ofFinite, AdelicGL.infinite_ofFinite,
      map_one]
  · rw [finite_inverseTranspose, AdelicGL.finite_ofFinite, AdelicGL.finite_ofFinite]

theorem inverseTranspose_ofInfinite (x : InfiniteAdelicGL F n) :
    GeneralLinear.inverseTranspose n (Adeles F) (AdelicGL.ofInfinite F n x) =
      AdelicGL.ofInfinite F n (GeneralLinear.inverseTranspose n _ x) := by
  refine AdelicGL.ext_infinite_finite F n ?_ ?_
  · rw [infinite_inverseTranspose, AdelicGL.infinite_ofInfinite, AdelicGL.infinite_ofInfinite]
  · rw [finite_inverseTranspose, AdelicGL.finite_ofInfinite, AdelicGL.finite_ofInfinite,
      map_one]

omit [NumberField F] in
/-- If `Z² = 0` then `(-ᵗZ)² = 0`. -/
theorem neg_transpose_mul_self_eq_zero {Z : ArchimedeanMatrix F n} (hZ : Z * Z = 0) :
    (-Z.transpose) * (-Z.transpose) = 0 := by
  rw [neg_mul_neg, ← Matrix.transpose_mul, hZ, Matrix.transpose_zero]

omit [NumberField F] in
/-- `ᵗ(1 + Z)⁻¹ = 1 - ᵗZ` for a square-zero archimedean matrix `Z`. -/
theorem inverseTranspose_squareZeroElement (Z : ArchimedeanMatrix F n) (hZ : Z * Z = 0) :
    GeneralLinear.inverseTranspose n (InfiniteAdeleRing F)
        (ArchimedeanGL.squareZeroElement Z hZ) =
      ArchimedeanGL.squareZeroElement (-Z.transpose) (neg_transpose_mul_self_eq_zero F hZ) := by
  unfold ArchimedeanGL.squareZeroElement
  change GeneralLinear.inverseTranspose n _ (Matrix.GeneralLinearGroup.map
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom
        (ArchimedeanGL.squareZeroUnit Z hZ)) =
    Matrix.GeneralLinearGroup.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom
      (ArchimedeanGL.squareZeroUnit (-Z.transpose) (neg_transpose_mul_self_eq_zero F hZ))
  rw [inverseTranspose_map]
  congr 1
  apply Units.ext
  change (1 - Z).transpose = 1 + -Z.transpose
  rw [Matrix.transpose_sub, Matrix.transpose_one, sub_eq_add_neg]

/-- Transpose inverse of a finite adelic point. -/
theorem iota_finitePoint (l : FiniteAdelicGL F n) :
    iota F n (finitePoint F n l) = finitePoint F n (GeneralLinear.inverseTranspose n _ l) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  rw [adelicEquiv_iota]
  unfold finitePoint
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, inverseTranspose_ofFinite]

/-- Transpose inverse of an archimedean square-zero point: `ι(1 + Z) = 1 - ᵗZ`. -/
theorem iota_archPoint (Z : ArchimedeanMatrix F n) (hZ : Z * Z = 0) :
    iota F n (archPoint F n Z hZ) =
      archPoint F n (-Z.transpose) (neg_transpose_mul_self_eq_zero F hZ) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  rw [adelicEquiv_iota]
  unfold archPoint
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, inverseTranspose_ofInfinite,
    inverseTranspose_squareZeroElement]

theorem archPoint_congr {Z Z' : ArchimedeanMatrix F n} (hZ : Z * Z = 0)
    (hZ' : Z' * Z' = 0) (h : Z = Z') : archPoint F n Z hZ = archPoint F n Z' hZ' := by
  subst h
  rfl

/-- Transpose inverse maps the rational subgroup into itself. -/
theorem iota_mem_rationalSubgroup {y : Points F n}
    (hy : y ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n)) :
    iota F n y ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n) := by
  obtain ⟨c, rfl⟩ := hy
  rw [iota_rational]
  exact ⟨_, rfl⟩

end Points

section Space

variable (n : ℕ)

/-- Composition with transpose inverse, `f ↦ f ∘ ι`, as a linear automorphism of the functions
on `GL_n(𝔸)`. -/
def iotaComp : (Points F n → ℂ) ≃ₗ[ℂ] (Points F n → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (iotaEquiv F n).toEquiv

theorem iotaComp_apply (f : Points F n → ℂ) (x : Points F n) :
    iotaComp F n f x = f (iota F n x) := rfl

variable {n} (V : Submodule ℂ (Points F n → ℂ))

/-- The space of the functions `f ∘ ι`, `f ∈ V`. -/
def iotaSpace : Submodule ℂ (Points F n → ℂ) :=
  V.map (iotaComp F n : (Points F n → ℂ) →ₗ[ℂ] (Points F n → ℂ))

/-- `f ↦ f ∘ ι` as a linear equivalence `V ≃ iotaSpace V`. -/
def iotaSpaceEquiv : V ≃ₗ[ℂ] iotaSpace F V :=
  (iotaComp F n).submoduleMap V

theorem coe_iotaSpaceEquiv (f : V) (x : Points F n) :
    ((iotaSpaceEquiv F V f : iotaSpace F V) : Points F n → ℂ) x = (f : Points F n → ℂ) (iota F n x) :=
  rfl

/-- Every function of `iotaSpace V` is `g ∘ ι` for its preimage `g ∈ V`. -/
theorem coe_iotaSpace (f : iotaSpace F V) (x : Points F n) :
    (f : Points F n → ℂ) x =
      (((iotaSpaceEquiv F V).symm f : V) : Points F n → ℂ) (iota F n x) := by
  rw [← coe_iotaSpaceEquiv, LinearEquiv.apply_symm_apply]

end Space

section Derivative

variable {r : ℕ} (V : Submodule ℂ (Points F (r + 1) → ℂ))
  (R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V)

/-- The archimedean derivatives on `iotaSpace V`: `Z` acts through `R(-ᵗZ)`, transported by
`f ↦ f ∘ ι`. -/
def iotaDerivative :
    ArchimedeanMatrix F (r + 1) →ₗ[ℝ] iotaSpace F V →ₗ[ℂ] iotaSpace F V where
  toFun Z := (iotaSpaceEquiv F V).toLinearMap ∘ₗ R (-Z.transpose) ∘ₗ
    (iotaSpaceEquiv F V).symm.toLinearMap
  map_add' Z₁ Z₂ := by
    rw [Matrix.transpose_add, neg_add, map_add, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c Z := by
    refine LinearMap.ext fun f => Subtype.ext (funext fun x => ?_)
    rw [Matrix.transpose_smul, ← smul_neg, map_smul]
    rfl

theorem coe_iotaDerivative (Z : ArchimedeanMatrix F (r + 1)) (f : iotaSpace F V)
    (x : Points F (r + 1)) :
    ((iotaDerivative F V R Z f : iotaSpace F V) : Points F (r + 1) → ℂ) x =
      ((R (-Z.transpose) ((iotaSpaceEquiv F V).symm f) : V) : Points F (r + 1) → ℂ)
        (iota F (r + 1) x) :=
  rfl

variable {F V R}

/-- **Transpose inverse preserves Whittaker decay classes.** -/
theorem whittakerDecayClass_iotaSpace (hV : WhittakerDecayClass F r V R) :
    WhittakerDecayClass F r (iotaSpace F V) (iotaDerivative F V R) where
  continuous f := by
    have h : (f : Points F (r + 1) → ℂ) =
        (((iotaSpaceEquiv F V).symm f : V) : Points F (r + 1) → ℂ) ∘ iota F (r + 1) :=
      funext (coe_iotaSpace F V f)
    rw [h]
    exact (hV.continuous _).comp (continuous_iota F (r + 1))
  rational f y hy x := by
    rw [coe_iotaSpace, coe_iotaSpace, iota_mul]
    exact hV.rational _ _ (iota_mem_rationalSubgroup F hy) _
  level f := by
    obtain ⟨L, hLo, hL⟩ := hV.level ((iotaSpaceEquiv F V).symm f)
    refine ⟨L.comap (GeneralLinear.inverseTranspose (r + 1) _).toMonoidHom,
      hLo.preimage (GeneralLinear.continuous_inverseTranspose (r + 1) _), fun x l hl => ?_⟩
    rw [coe_iotaSpace, coe_iotaSpace, iota_mul, iota_finitePoint]
    exact hL _ _ hl
  bounded f lo hi hlo := by
    have hm : 0 < max hi lo := lt_max_of_lt_right hlo
    obtain ⟨B, hB⟩ := hV.bounded ((iotaSpaceEquiv F V).symm f) (max hi lo)⁻¹ lo⁻¹
      (inv_pos.mpr hm)
    refine ⟨B, fun x hlx hhx => ?_⟩
    have hx := detNorm_pos F (r + 1) x
    rw [coe_iotaSpace]
    refine hB _ ?_ ?_
    · rw [detNorm_iota]
      exact inv_anti₀ hx (hhx.trans (le_max_left hi lo))
    · rw [detNorm_iota]
      exact inv_anti₀ hlo hlx
  deriv f Z hZ x := by
    have h := hV.deriv ((iotaSpaceEquiv F V).symm f) (-Z.transpose)
      (neg_transpose_mul_self_eq_zero F hZ) (iota F (r + 1) x)
    rw [← coe_iotaDerivative] at h
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have e : -(t • Z).transpose = t • -Z.transpose := by
      rw [Matrix.transpose_smul, smul_neg]
    dsimp only
    rw [coe_iotaSpace F V f, iota_mul, iota_archPoint, archPoint_congr F _ _ e]

end Derivative

end Langlands.Global.RankinSelbergGlobal.Unfolding
