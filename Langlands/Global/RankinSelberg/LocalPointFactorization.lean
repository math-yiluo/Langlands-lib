import Langlands.Global.RankinSelberg.UnfoldingGL
import Langlands.Global.RankinSelberg.PartialIntegralExhaustion
import Langlands.Group.GL.PrincipalLevelDominance
import Langlands.Global.RankinSelberg.WhittakerCellDecompositionStatement
import Langlands.Representation.Whittaker.Spherical
import Langlands.Representation.Conductor.Congruence
import Langlands.Global.RankinSelberg.UnequalIntegrals
import Langlands.Global.AdelicBlockDeterminantCharacter
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.Global.Factors.HeckeEulerProduct

/-! # Points supported at one finite place

Generic lemmas for the one-place step of the unramified Euler factorizations: Iwasawa
exponents of `ϖ ^ λ u k`, products of spherical Whittaker functions with mutually inverse
characters, the points `ι_v(h)` of `GL_m(𝔸)` supported at one finite place, a uniformizer of
`F_v` for both valuations of the completion, and the determinant of `ι_v(h)`. See the paired
Markdown.
-/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj WithZero
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.LocalPointFactorization

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical

/-! ### Local lemmas over a valued field -/

section Local

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {w : Valuation K Γ₀}

/-- Conjugation by `ϖ ^ lam` preserves the upper unipotent group. -/
theorem torus_mul_mul_inv_mem {n : ℕ} (ϖ : Kˣ) (lam : Fin (n + 1) → ℤ)
    {u : Matrix.GeneralLinearGroup (Fin (n + 1)) K} (hu : u ∈ Langlands.GeneralLinear.upperUnipotent (n + 1) K) :
    torus ϖ lam * u * (torus ϖ lam)⁻¹ ∈ Langlands.GeneralLinear.upperUnipotent (n + 1) K := by
  have happ : ∀ i j, (torus ϖ lam * u * (torus ϖ lam)⁻¹) i j =
      ((ϖ ^ lam i : Kˣ) : K) * u i j * (((ϖ ^ lam j)⁻¹ : Kˣ) : K) := by
    intro i j
    rw [torus_inv, torus]
    exact Langlands.GeneralLinear.Iwasawa.diagonalUnits_mul_mul_apply _ _ _ _ _
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (torus ϖ lam * u * (torus ϖ lam)⁻¹) i j = 0
    rw [happ, hu.1 hij, mul_zero, zero_mul]
  · rw [happ, hu.2 i, mul_one, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _)]

/-- The Iwasawa exponent of `ϖ ^ lam u k` is `lam`. -/
theorem exponent_torus_mul {n : ℕ} {ϖ : Kˣ} (hϖ : IsUniformizingElement w ϖ)
    (lam : Fin (n + 1) → ℤ) {u k : Matrix.GeneralLinearGroup (Fin (n + 1)) K}
    (hu : u ∈ Langlands.GeneralLinear.upperUnipotent (n + 1) K) (hk : k ∈ Langlands.Conductor.integralSubgroup w.integer n) :
    exponent hϖ (torus ϖ lam * (u * k)) = lam :=
  exponent_eq hϖ (torus_mul_mul_inv_mem ϖ lam hu) hk (by group)

/-- The Iwasawa exponent of `u k` is zero. -/
theorem exponent_unipotent_mul_integral {n : ℕ} {ϖ : Kˣ} (hϖ : IsUniformizingElement w ϖ)
    {u k : Matrix.GeneralLinearGroup (Fin (n + 1)) K}
    (hu : u ∈ Langlands.GeneralLinear.upperUnipotent (n + 1) K) (hk : k ∈ Langlands.Conductor.integralSubgroup w.integer n) :
    exponent hϖ (u * k) = 0 :=
  exponent_eq hϖ hu hk (by rw [Langlands.GeneralLinear.torus_zero, mul_one])

/-- The product of two cell functions whose characters are mutually inverse: the
characters cancel, so no integrality of the characters is needed. -/
theorem cellFunction_mul_cellFunction {n : ℕ} {ϖ : Kˣ} (hϖ : IsUniformizingElement w ϖ)
    {θ θ' : Langlands.GeneralLinear.upperUnipotent (n + 1) K →* ℂˣ} (hθ : ∀ u, θ u * θ' u = 1)
    (c c' : (Fin (n + 1) → ℤ) → ℂ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) K) :
    cellFunction hϖ θ c g * cellFunction hϖ θ' c' g =
      (if Antitone (exponent hϖ g) then c (exponent hϖ g) else 0) *
        (if Antitone (exponent hϖ g) then c' (exponent hϖ g) else 0) := by
  unfold cellFunction
  split_ifs with h
  · have h1 := congrArg (fun z : ℂˣ => (z : ℂ)) (hθ (unipotentPart hϖ g))
    simp only [Units.val_mul, Units.val_one] at h1
    calc _ = ((θ (unipotentPart hϖ g) : ℂ) * (θ' (unipotentPart hϖ g) : ℂ)) *
          (c (exponent hϖ g) * c' (exponent hϖ g)) := by ring
      _ = _ := by rw [h1, one_mul]
  · rw [mul_zero]

/-- `W°_θ(g; a) W°_θ'(g; b)` for mutually inverse `θ`, `θ'` and a point `g` of exponent
`lam`. -/
theorem sphericalWhittaker_mul_sphericalWhittaker {n : ℕ} {ϖ : Kˣ}
    (hϖ : IsUniformizingElement w ϖ) {θ θ' : Langlands.GeneralLinear.upperUnipotent (n + 1) K →* ℂˣ}
    (hθ : ∀ u, θ u * θ' u = 1) (q : ℕ) (a b : Fin (n + 1) → ℂˣ)
    {g : Matrix.GeneralLinearGroup (Fin (n + 1)) K} {lam : Fin (n + 1) → ℤ}
    (hg : exponent hϖ g = lam) :
    sphericalWhittaker hϖ θ q a g * sphericalWhittaker hϖ θ' q b g =
      (if Antitone lam then halfModulus q lam * satakeSchur a lam else 0) *
        (if Antitone lam then halfModulus q lam * satakeSchur b lam else 0) := by
  rw [sphericalWhittaker, sphericalWhittaker, cellFunction_mul_cellFunction hϖ hθ, hg]

theorem sphericalWhittaker_mul_sphericalWhittaker_of_exponent_eq_zero {n : ℕ} {ϖ : Kˣ}
    (hϖ : IsUniformizingElement w ϖ) {θ θ' : Langlands.GeneralLinear.upperUnipotent (n + 1) K →* ℂˣ}
    (hθ : ∀ u, θ u * θ' u = 1) (q : ℕ) (a b : Fin (n + 1) → ℂˣ)
    {g : Matrix.GeneralLinearGroup (Fin (n + 1)) K} (hg : exponent hϖ g = 0) :
    sphericalWhittaker hϖ θ q a g * sphericalWhittaker hϖ θ' q b g = 1 := by
  rw [sphericalWhittaker_mul_sphericalWhittaker hϖ hθ q a b hg, halfModulus_zero,
    satakeSchur_zero, satakeSchur_zero]
  have h0 : Antitone (0 : Fin (n + 1) → ℤ) := fun _ _ _ => le_rfl
  simp only [h0, ↓reduceIte, mul_one]

/-- Equivalent valuations have the same uniformizing elements. -/
theorem isUniformizingElement_of_isEquiv {Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₁]
    {w₁ : Valuation K Γ₁} (h : w.IsEquiv w₁) {ϖ : Kˣ} (hϖ : IsUniformizingElement w ϖ) :
    IsUniformizingElement w₁ ϖ := by
  refine ⟨h.lt_one_iff_lt_one.mp hϖ.1, fun x hx => ?_⟩
  obtain ⟨m, hm⟩ := hϖ.2 x hx
  refine ⟨m, ?_⟩
  rw [← map_zpow₀] at hm ⊢
  exact h.eq_iff.mp hm

/-- Equivalent valuations have the same integers. -/
theorem integer_eq_of_isEquiv {Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₁]
    {w₁ : Valuation K Γ₁} (h : w.IsEquiv w₁) : w.integer = w₁.integer := by
  ext x
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff]
  exact h.le_one_iff_le_one

end Local

/-! ### Points supported at one finite place -/

section LocalPoint

local instance pointwiseSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance pointwiseSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

theorem finite_ofFinite (m : ℕ) (x : FiniteAdelicGL F m) :
    AdelicGL.finite F m (AdelicGL.ofFinite F m x) = x := by
  apply Units.ext; rfl

theorem infinite_ofFinite (m : ℕ) (x : FiniteAdelicGL F m) :
    AdelicGL.infinite F m (AdelicGL.ofFinite F m x) = 1 := by
  apply Units.ext; rfl

theorem adelicEquiv_localPoint (m : ℕ) (v : FinitePlace F) (h : FiniteLocalGL F m v) :
    GeneralLinearGroupPoints.adelicEquiv F m (localPoint F m v h) =
      AdelicGL.ofFinite F m (FiniteAdelicGL.localInclusion F m v h) := by
  rw [localPoint, MulEquiv.apply_symm_apply]

theorem finiteComponent_inv (m : ℕ) (v : FinitePlace F) (g : Points F m) :
    finiteComponent F m v g⁻¹ = (finiteComponent F m v g)⁻¹ := by
  simp only [finiteComponent, map_inv]

theorem finiteComponent_localPoint (m : ℕ) (v : FinitePlace F) (h : FiniteLocalGL F m v) :
    finiteComponent F m v (localPoint F m v h) = h := by
  rw [finiteComponent, adelicEquiv_localPoint, finite_ofFinite,
    FiniteAdelicGL.localProjection_localInclusion]

theorem finiteComponent_localPoint_of_ne (m : ℕ) {v w : FinitePlace F} (hw : w ≠ v)
    (h : FiniteLocalGL F m v) : finiteComponent F m w (localPoint F m v h) = 1 := by
  rw [finiteComponent, adelicEquiv_localPoint, finite_ofFinite,
    FiniteAdelicGL.localProjection_localInclusion_of_ne F m v w hw]

theorem localPoint_mul (m : ℕ) (v : FinitePlace F) (h h' : FiniteLocalGL F m v) :
    localPoint F m v (h * h') = localPoint F m v h * localPoint F m v h' := by
  simp only [localPoint, map_mul]

/-- `ι_v(h)` commutes with every point whose component at `v` is the identity. -/
theorem localPoint_mul_comm (m : ℕ) (v : FinitePlace F) (h : FiniteLocalGL F m v)
    {g : Points F m} (hg : finiteComponent F m v g = 1) :
    localPoint F m v h * g = g * localPoint F m v h := by
  apply (GeneralLinearGroupPoints.adelicEquiv F m).injective
  rw [map_mul, map_mul, adelicEquiv_localPoint]
  set G := GeneralLinearGroupPoints.adelicEquiv F m g
  rw [← AdelicGL.pair_projections F m
      (AdelicGL.ofFinite F m (FiniteAdelicGL.localInclusion F m v h) * G),
    ← AdelicGL.pair_projections F m
      (G * AdelicGL.ofFinite F m (FiniteAdelicGL.localInclusion F m v h))]
  congr 1
  · rw [map_mul, map_mul, infinite_ofFinite, one_mul, mul_one]
  · rw [map_mul, map_mul, finite_ofFinite]
    apply FiniteAdelicGL.ext_localProjection
    intro w
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      have h1 : FiniteAdelicGL.localProjection F m w (AdelicGL.finite F m G) = 1 := hg
      rw [h1, FiniteAdelicGL.localProjection_localInclusion, one_mul, mul_one]
    · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne F m v w hw, one_mul, mul_one]

/-- The point `g ι_v(g_v)⁻¹` has identity component at `v`. -/
theorem finiteComponent_mul_inv_localPoint (m : ℕ) (v : FinitePlace F) (g : Points F m) :
    finiteComponent F m v (g * (localPoint F m v (finiteComponent F m v g))⁻¹) = 1 := by
  rw [finiteComponent_mul, finiteComponent_inv, finiteComponent_localPoint, mul_inv_cancel]

/-- `ι_v(h) g = g' ι_v(h g_v)` with `g' = g ι_v(g_v)⁻¹`. -/
theorem localPoint_mul_eq (m : ℕ) (v : FinitePlace F) (h : FiniteLocalGL F m v)
    (g : Points F m) :
    localPoint F m v h * g =
      (g * (localPoint F m v (finiteComponent F m v g))⁻¹) *
        localPoint F m v (h * finiteComponent F m v g) := by
  rw [localPoint_mul, ← mul_assoc, ← localPoint_mul_comm F m v h
    (finiteComponent_mul_inv_localPoint F m v g)]
  group

end LocalPoint

/-! ### The uniformizer of `F_v` -/

/-- An element of value `exp (-1)` for a `ℤᵐ⁰`-valued valuation is uniformizing. -/
theorem isUniformizingElement_of_eq_exp {K : Type*} [Field K] (w : Valuation K ℤᵐ⁰) (ϖ : Kˣ)
    (h : w (ϖ : K) = WithZero.exp (-1)) : IsUniformizingElement w ϖ := by
  refine ⟨?_, fun x hx => ⟨-WithZero.log (w x), ?_⟩⟩
  · rw [h, WithZero.exp_lt_one_iff]
    norm_num
  · rw [h, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one, neg_neg,
      WithZero.exp_log ((Valuation.ne_zero_iff w).2 hx)]

section Uniformizer

variable {F : Type u} [Field F] [NumberField F]

/-- The uniformizer `ϖ_v` of `F_v` specified by the local realization
`CompletionPadic.topologicalData v`. -/
def placeUniformizer (v : FinitePlace F) : (FiniteCompletion F v)ˣ :=
  LocalFactor.PadicAbelian.uniformizerUnit (CompletionPadic.topologicalData v)

theorem valued_placeUniformizer (v : FinitePlace F) :
    (Valued.v : Valuation (FiniteCompletion F v) ℤᵐ⁰) (placeUniformizer v : FiniteCompletion F v) =
      WithZero.exp (-1) := by
  rw [placeUniformizer,
    ← AdelicFunctoriality.FiniteExtension.topologicalData_discreteValuation v]
  simpa using
    LocalFactor.PadicAbelian.uniformizerUnit_zpow_value (CompletionPadic.topologicalData v) 1

/-- `ϖ_v` is uniformizing for the valuation of the completion. -/
theorem isUniformizingElement_valued (v : FinitePlace F) :
    IsUniformizingElement (Valued.v : Valuation (FiniteCompletion F v) ℤᵐ⁰)
      (placeUniformizer v) :=
  isUniformizingElement_of_eq_exp _ _ (valued_placeUniformizer v)

/-- The completion valuation and the canonical valuation of `padicField v` are equivalent. -/
theorem valued_isEquiv_canonical (v : FinitePlace F) :
    (Valued.v : Valuation (FiniteCompletion F v) ℤᵐ⁰).IsEquiv
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel) :=
  (AdelicFunctoriality.valuativeRel_valuation_isEquiv (CompletionPadic.topologicalData v)
    Valued.v (CompletionPadic.topologicalData_vle v)).symm

/-- `ϖ_v` is uniformizing for the canonical valuation of `padicField v`. -/
theorem isUniformizingElement_canonical (v : FinitePlace F) :
    IsUniformizingElement
      (@ValuativeRel.valuation _ _
        (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel)
      (placeUniformizer v) :=
  isUniformizingElement_of_isEquiv (valued_isEquiv_canonical v) (isUniformizingElement_valued v)

theorem norm_placeUniformizer (v : FinitePlace F) :
    ‖(placeUniformizer v : FiniteCompletion F v)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ :=
  HeckeEulerProduct.norm_uniformizerUnit v

/-- `x ∈ N(F_v) GL(𝒪_v)` gives `x = u k` with `u` unitriangular and `k` integral for the
canonical valuation. -/
theorem exists_eq_mul_of_isUnipotentIntegral (v : FinitePlace F) {m : ℕ}
    {x : FiniteLocalGL F (m + 1) v} (hx : IsUnipotentIntegral F (m + 1) v x) :
    ∃ u ∈ Langlands.GeneralLinear.upperUnipotent (m + 1) (FiniteCompletion F v),
      ∃ k ∈ Langlands.Conductor.integralSubgroup
        (@ValuativeRel.valuation _ _
          (CompletionPadic.padicField v).canonicalTopologicalData.valuativeRel).integer m,
        x = u * k := by
  obtain ⟨k0, hk0, hdiag, hlow⟩ := hx
  rw [FiniteAdelicGL.mem_localIntegral] at hk0
  refine ⟨x * k0, ⟨fun i j hij => hlow i j hij, hdiag⟩, k0⁻¹, ?_, by group⟩
  rw [Langlands.Conductor.mem_integralSubgroup, ← integer_eq_of_isEquiv (valued_isEquiv_canonical v)]
  refine ⟨fun i j => (Valuation.mem_integer_iff _ _).2 (hk0.2 i j),
    fun i j => (Valuation.mem_integer_iff _ _).2 ?_⟩
  rw [inv_inv]
  exact hk0.1 i j

end Uniformizer

/-! ### The determinant -/

section Determinant

variable (F : Type u) [Field F] [NumberField F]

theorem detNorm_localPoint (m : ℕ) (v : FinitePlace F) (h : FiniteLocalGL F m v) :
    detNorm F m (localPoint F m v h) = ‖(Matrix.GeneralLinearGroup.det h).val‖ := by
  rw [detNorm, adelicEquiv_localPoint]
  exact AdelicBlockDeterminantCharacter.coe_determinantNorm_localInclusion F m v h

theorem detNorm_ne_zero (m : ℕ) (g : Points F m) : detNorm F m g ≠ 0 := by
  rw [detNorm, NNReal.coe_ne_zero]
  exact Units.ne_zero _

theorem detPower_localPoint_mul (m : ℕ) (v : FinitePlace F) (h : FiniteLocalGL F m v)
    (g : Points F m) (s : ℂ) :
    detPower F m (localPoint F m v h * g) s =
      Complex.exp (s * (Real.log ‖(Matrix.GeneralLinearGroup.det h).val‖ : ℂ)) *
        detPower F m g s := by
  have h0 : ‖(Matrix.GeneralLinearGroup.det h).val‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Units.ne_zero _)
  rw [detPower, detPower, Unfolding.detNorm_mul, detNorm_localPoint,
    Real.log_mul h0 (detNorm_ne_zero F m g), ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {F}

/-- `log ‖det ϖ_v ^ lam‖ = -(∑ lam) log N(v)`. -/
theorem log_norm_det_torus {m : ℕ} (v : FinitePlace F) (lam : Fin m → ℤ) :
    Real.log ‖(Matrix.GeneralLinearGroup.det (torus (placeUniformizer v) lam)).val‖ =
      -((∑ i, lam i : ℤ) : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  have hdet : (Matrix.GeneralLinearGroup.det (torus (placeUniformizer v) lam)).val =
      ∏ i, (((placeUniformizer v ^ lam i : (FiniteCompletion F v)ˣ)) : FiniteCompletion F v) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, torus_val, Matrix.det_diagonal]
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      ‖(((placeUniformizer v ^ lam i : (FiniteCompletion F v)ˣ)) : FiniteCompletion F v)‖ ≠ 0 :=
    fun i _ => norm_ne_zero_iff.2 (Units.ne_zero _)
  rw [hdet, norm_prod, Real.log_prod hne]
  simp only [Units.val_zpow_eq_zpow_val, norm_zpow, norm_placeUniformizer, Real.log_zpow,
    Real.log_inv]
  push_cast
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end Determinant

end Langlands.Global.RankinSelbergGlobal.LocalPointFactorization
