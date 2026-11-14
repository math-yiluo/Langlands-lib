import Langlands.Representation.Archimedean.StandardModule
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# `K`-finite principal-series functions are stable under `K` and `𝔤`

For `F = ℝ` or `ℂ` (any `RCLike F`), the `K`-finite functions of the Library's smooth principal
series `principalSeries F N χ` of `GL_N(F)`, `K = unitaryCompact F N`, are stable under right
translation by `K` and under the right derivative along every real direction
`X ∈ 𝔤𝔩_N(F)`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

universe uF

variable {F : Type uF} [RCLike F] {N : ℕ}

/-! ## Functions on `GL_N(F)` in matrix coordinates -/

open Classical in
/-- The extension of a function on `GL_N(F)` to all matrices, by `0` off the units. -/
def unitsExtension (φ : Langlands.GeneralLinear N F → ℂ) (y : Matrix (Fin N) (Fin N) F) : ℂ :=
  if h : IsUnit y then φ h.unit else 0

theorem unitsExtension_val (φ : Langlands.GeneralLinear N F → ℂ)
    (g : Langlands.GeneralLinear N F) :
    unitsExtension φ (g : Matrix (Fin N) (Fin N) F) = φ g := by
  simp [unitsExtension, Units.isUnit g]

theorem isOpen_setOf_isUnit_matrix :
    IsOpen {y : Matrix (Fin N) (Fin N) F | IsUnit y} :=
  Units.isOpen

theorem range_val_eq_setOf_isUnit :
    Set.range (Units.val : Langlands.GeneralLinear N F → Matrix (Fin N) (Fin N) F) =
      {y | IsUnit y} := by
  ext y
  simp [IsUnit]

/-- The manifold derivative of the inclusion of `GL_N(F)` into the matrices is the identity. -/
theorem mfderiv_units_val (x : Langlands.GeneralLinear N F) :
    mfderiv (matrixModel F N) (matrixModel F N)
        (Units.val : Langlands.GeneralLinear N F → Matrix (Fin N) (Fin N) F) x =
      ContinuousLinearMap.id ℝ _ := by
  have h : (Units.val : Langlands.GeneralLinear N F → Matrix (Fin N) (Fin N) F) =
      extChartAt (matrixModel F N) x := rfl
  rw [h, mfderiv_extChartAt_self]

/-- In matrix coordinates the manifold derivative of `φ = ψ ∘ val` is the derivative of `ψ`. -/
theorem mfderiv_eq_fderiv_of_eq_comp {φ : Langlands.GeneralLinear N F → ℂ}
    {ψ : Matrix (Fin N) (Fin N) F → ℂ} (hφ : ∀ h, φ h = ψ h) (x : Langlands.GeneralLinear N F)
    (hψ : DifferentiableAt ℝ ψ (x : Matrix (Fin N) (Fin N) F)) :
    mfderiv (matrixModel F N) 𝓘(ℝ, ℂ) φ x = fderiv ℝ ψ (x : Matrix (Fin N) (Fin N) F) := by
  have hfun : φ = ψ ∘ Units.val := funext hφ
  subst hfun
  rw [mfderiv_comp x hψ.mdifferentiableAt
    ((Units.contMDiff_val (n := ∞)).mdifferentiableAt (by simp)), mfderiv_units_val,
    mfderiv_eq_fderiv]
  rfl

theorem unitsExtension_of_not_isUnit (φ : Langlands.GeneralLinear N F → ℂ)
    {y : Matrix (Fin N) (Fin N) F} (hy : ¬IsUnit y) : unitsExtension φ y = 0 := by
  simp [unitsExtension, hy]

theorem unitsExtension_add (φ₁ φ₂ : Langlands.GeneralLinear N F → ℂ)
    (y : Matrix (Fin N) (Fin N) F) :
    unitsExtension (φ₁ + φ₂) y = unitsExtension φ₁ y + unitsExtension φ₂ y := by
  by_cases hy : IsUnit y
  · obtain ⟨g, rfl⟩ := hy
    simp only [unitsExtension_val, Pi.add_apply]
  · simp [unitsExtension_of_not_isUnit _ hy]

theorem unitsExtension_smul (c : ℂ) (φ : Langlands.GeneralLinear N F → ℂ)
    (y : Matrix (Fin N) (Fin N) F) :
    unitsExtension (c • φ) y = c * unitsExtension φ y := by
  by_cases hy : IsUnit y
  · obtain ⟨g, rfl⟩ := hy
    simp only [unitsExtension_val, Pi.smul_apply, smul_eq_mul]
  · simp [unitsExtension_of_not_isUnit _ hy]

/-- The extension of a right translate is the extension composed with right multiplication. -/
theorem unitsExtension_rightTranslation (φ : Langlands.GeneralLinear N F → ℂ)
    (k : Langlands.GeneralLinear N F) (y : Matrix (Fin N) (Fin N) F) :
    unitsExtension (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) k φ) y =
      unitsExtension φ (y * (k : Matrix (Fin N) (Fin N) F)) := by
  by_cases hy : IsUnit y
  · obtain ⟨g, rfl⟩ := hy
    rw [unitsExtension_val, ← Units.val_mul, unitsExtension_val]
    rfl
  · have hyk : ¬IsUnit (y * (k : Matrix (Fin N) (Fin N) F)) :=
      fun h => hy ((Units.isUnit_mul_units y k).mp h)
    rw [unitsExtension_of_not_isUnit _ hy, unitsExtension_of_not_isUnit _ hyk]

/-- A smooth function on `GL_N(F)` extends to a smooth function on the open set of invertible
matrices. -/
theorem contDiffOn_unitsExtension {φ : Langlands.GeneralLinear N F → ℂ}
    (hφ : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ φ) :
    ContDiffOn ℝ ∞ (unitsExtension φ) {y : Matrix (Fin N) (Fin N) F | IsUnit y} := by
  have hemb : Topology.IsOpenEmbedding
      (Units.val : Langlands.GeneralLinear N F → Matrix (Fin N) (Fin N) F) :=
    Units.isOpenEmbedding_val
  have hsymm := contMDiffOn_isOpenEmbedding_symm (I := matrixModel F N) (n := ∞) hemb
  have hc := hφ.comp_contMDiffOn hsymm
  rw [contMDiffOn_iff_contDiffOn] at hc
  rw [← range_val_eq_setOf_isUnit]
  refine hc.congr ?_
  rintro _ ⟨g, rfl⟩
  rw [unitsExtension_val, Function.comp_apply, hemb.toOpenPartialHomeomorph_left_inv]

theorem differentiableAt_unitsExtension {φ : Langlands.GeneralLinear N F → ℂ}
    (hφ : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ φ) {y : Matrix (Fin N) (Fin N) F}
    (hy : IsUnit y) : DifferentiableAt ℝ (unitsExtension φ) y :=
  ((contDiffOn_unitsExtension hφ).differentiableOn (by simp)).differentiableAt
    (isOpen_setOf_isUnit_matrix.mem_nhds hy)

/-- A function on `GL_N(F)` that agrees with a smooth function on the invertible matrices is
smooth. -/
theorem contMDiff_of_contDiffOn {φ : Langlands.GeneralLinear N F → ℂ}
    {ψ : Matrix (Fin N) (Fin N) F → ℂ}
    (hψ : ContDiffOn ℝ ∞ ψ {y : Matrix (Fin N) (Fin N) F | IsUnit y})
    (hφ : ∀ g : Langlands.GeneralLinear N F, φ g = ψ g) :
    ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ φ := by
  have h : φ = ψ ∘ Units.val := funext hφ
  rw [h]
  exact (contMDiffOn_iff_contDiffOn.mpr hψ).comp_contMDiff Units.contMDiff_val
    fun g => Units.isUnit g

/-! ## The right derivative in matrix coordinates -/

theorem differentiableAt_unitsExtension_mul_left {f : Langlands.GeneralLinear N F → ℂ}
    (hf : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f) (g : Langlands.GeneralLinear N F) :
    DifferentiableAt ℝ
      (fun y : Matrix (Fin N) (Fin N) F => unitsExtension f ((g : Matrix (Fin N) (Fin N) F) * y))
      1 := by
  have h1 : DifferentiableAt ℝ (unitsExtension f) ((g : Matrix (Fin N) (Fin N) F) * 1) := by
    rw [mul_one]
    exact differentiableAt_unitsExtension hf (Units.isUnit g)
  exact h1.comp (1 : Matrix (Fin N) (Fin N) F)
    (differentiableAt_id.const_mul (g : Matrix (Fin N) (Fin N) F))

/-- `(R(X) f)(g)` is the derivative at `1` of `y ↦ f(g y)` on matrices, applied to `X`. -/
theorem rightDerivative_eq_fderiv_mul_left {f : Langlands.GeneralLinear N F → ℂ}
    (hf : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f) (X : Matrix (Fin N) (Fin N) F)
    (g : Langlands.GeneralLinear N F) :
    rightDerivative (matrixModel F N) X f g =
      fderiv ℝ
        (fun y : Matrix (Fin N) (Fin N) F => unitsExtension f ((g : Matrix (Fin N) (Fin N) F) * y))
        1 X := by
  have h := mfderiv_eq_fderiv_of_eq_comp (φ := fun h => f (g * h))
    (ψ := fun y : Matrix (Fin N) (Fin N) F =>
      unitsExtension f ((g : Matrix (Fin N) (Fin N) F) * y))
    (fun h => by rw [← Units.val_mul, unitsExtension_val]) 1
    (by simpa using differentiableAt_unitsExtension_mul_left hf g)
  rw [Units.val_one] at h
  exact congrArg (fun L => L X) h

/-- `(R(X) f)(g) = d f̃_g (g X)` where `f̃` is the extension of `f` to the matrices. -/
theorem rightDerivative_eq_fderiv {f : Langlands.GeneralLinear N F → ℂ}
    (hf : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f) (X : Matrix (Fin N) (Fin N) F)
    (g : Langlands.GeneralLinear N F) :
    rightDerivative (matrixModel F N) X f g =
      fderiv ℝ (unitsExtension f) (g : Matrix (Fin N) (Fin N) F)
        ((g : Matrix (Fin N) (Fin N) F) * X) := by
  rw [rightDerivative_eq_fderiv_mul_left hf]
  have h1 : HasFDerivAt (unitsExtension f)
      (fderiv ℝ (unitsExtension f) ((g : Matrix (Fin N) (Fin N) F) * 1))
      ((g : Matrix (Fin N) (Fin N) F) * 1) := by
    rw [mul_one]
    exact (differentiableAt_unitsExtension hf (Units.isUnit g)).hasFDerivAt
  have h2 : HasFDerivAt
      (fun y : Matrix (Fin N) (Fin N) F => unitsExtension f ((g : Matrix (Fin N) (Fin N) F) * y))
      ((fderiv ℝ (unitsExtension f) ((g : Matrix (Fin N) (Fin N) F) * 1)).comp
        ((g : Matrix (Fin N) (Fin N) F) • ContinuousLinearMap.id ℝ _)) 1 :=
    h1.comp (1 : Matrix (Fin N) (Fin N) F)
      ((hasFDerivAt_id (1 : Matrix (Fin N) (Fin N) F)).const_mul (g : Matrix (Fin N) (Fin N) F))
  rw [h2.fderiv]
  simp

/-- The right derivative of a smooth function is smooth. -/
theorem contMDiff_rightDerivative {f : Langlands.GeneralLinear N F → ℂ}
    (hf : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f) (X : Matrix (Fin N) (Fin N) F) :
    ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ (rightDerivative (matrixModel F N) X f) := by
  have hd := ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_setOf_isUnit_matrix).mp
    (contDiffOn_unitsExtension hf)).2
  have hY : ContDiffOn ℝ ∞
      (fun y : Matrix (Fin N) (Fin N) F => fderiv ℝ (unitsExtension f) y (y * X))
      {y : Matrix (Fin N) (Fin N) F | IsUnit y} :=
    hd.clm_apply (contDiff_id.mul contDiff_const).contDiffOn
  exact contMDiff_of_contDiffOn hY fun g => rightDerivative_eq_fderiv hf X g

/-- Left equivariance passes to the right derivative. -/
theorem rightDerivative_mul_left_of_eq {f : Langlands.GeneralLinear N F → ℂ}
    (hf : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f) {a : Langlands.GeneralLinear N F} {c : ℂ}
    (ha : ∀ g, f (a * g) = c * f g) (X : Matrix (Fin N) (Fin N) F)
    (g : Langlands.GeneralLinear N F) :
    rightDerivative (matrixModel F N) X f (a * g) =
      c * rightDerivative (matrixModel F N) X f g := by
  have hfun : (fun h => f (a * g * h)) = fun h => c * f (g * h) :=
    funext fun h => by rw [mul_assoc, ha]
  have hdiff := differentiableAt_unitsExtension_mul_left hf g
  have h := mfderiv_eq_fderiv_of_eq_comp (φ := fun h => c * f (g * h))
    (ψ := fun y : Matrix (Fin N) (Fin N) F =>
      c * unitsExtension f ((g : Matrix (Fin N) (Fin N) F) * y))
    (fun h => by rw [← Units.val_mul, unitsExtension_val]) 1
    (by simpa using hdiff.const_mul c)
  change mfderiv (matrixModel F N) 𝓘(ℝ, ℂ) (fun h => f (a * g * h)) 1 X = _
  rw [rightDerivative_eq_fderiv_mul_left hf X g, hfun, h, Units.val_one,
    fderiv_const_mul hdiff]
  rfl

/-- Right translation by `k` conjugates the right derivative:
`R(k) (R(X) f) = R(k X k⁻¹) (R(k) f)`. -/
theorem rightTranslation_rightDerivative {f : Langlands.GeneralLinear N F → ℂ}
    (hf : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f) (X : Matrix (Fin N) (Fin N) F)
    (k : Langlands.GeneralLinear N F) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) k
        (rightDerivative (matrixModel F N) X f) =
      rightDerivative (matrixModel F N)
        ((k : Matrix (Fin N) (Fin N) F) * X * ((k⁻¹ : Langlands.GeneralLinear N F) :
          Matrix (Fin N) (Fin N) F))
        (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) k f) := by
  have hfk : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞
      (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) k f) :=
    hf.comp contMDiff_mul_right
  funext g
  change rightDerivative (matrixModel F N) X f (g * k) = _
  rw [rightDerivative_eq_fderiv_mul_left hf, rightDerivative_eq_fderiv_mul_left hfk]
  have hψ := differentiableAt_unitsExtension_mul_left hf (g * k)
  have hC1 : ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin N) (Fin N) F)
      ((k⁻¹ : Langlands.GeneralLinear N F) : Matrix (Fin N) (Fin N) F)
      (k : Matrix (Fin N) (Fin N) F) 1 = 1 := by
    simp [ContinuousLinearMap.mulLeftRight_apply]
  have h2 : HasFDerivAt
      (fun y : Matrix (Fin N) (Fin N) F =>
        unitsExtension f (((g * k : Langlands.GeneralLinear N F) : Matrix (Fin N) (Fin N) F) * y))
      (fderiv ℝ (fun y : Matrix (Fin N) (Fin N) F =>
        unitsExtension f (((g * k : Langlands.GeneralLinear N F) : Matrix (Fin N) (Fin N) F) * y))
          1)
      (ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin N) (Fin N) F)
        ((k⁻¹ : Langlands.GeneralLinear N F) : Matrix (Fin N) (Fin N) F)
        (k : Matrix (Fin N) (Fin N) F) 1) := by
    rw [hC1]
    exact hψ.hasFDerivAt
  have h3 := h2.comp (1 : Matrix (Fin N) (Fin N) F)
    (ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin N) (Fin N) F)
      ((k⁻¹ : Langlands.GeneralLinear N F) : Matrix (Fin N) (Fin N) F)
      (k : Matrix (Fin N) (Fin N) F)).hasFDerivAt
  have hfun : (fun y : Matrix (Fin N) (Fin N) F => unitsExtension
      (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) k f)
      ((g : Matrix (Fin N) (Fin N) F) * y)) =
      (fun y : Matrix (Fin N) (Fin N) F =>
        unitsExtension f (((g * k : Langlands.GeneralLinear N F) : Matrix (Fin N) (Fin N) F) * y)) ∘
      (ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin N) (Fin N) F)
        ((k⁻¹ : Langlands.GeneralLinear N F) : Matrix (Fin N) (Fin N) F)
        (k : Matrix (Fin N) (Fin N) F)) := by
    funext y
    rw [unitsExtension_rightTranslation, Function.comp_apply,
      ContinuousLinearMap.mulLeftRight_apply, Units.val_mul]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  rw [hfun, h3.fderiv]
  simp [ContinuousLinearMap.mulLeftRight_apply, mul_assoc]

/-! ## Linearity of the right derivative -/

theorem rightDerivative_add {f₁ f₂ : Langlands.GeneralLinear N F → ℂ}
    (hf₁ : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f₁)
    (hf₂ : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f₂) (X : Matrix (Fin N) (Fin N) F) :
    rightDerivative (matrixModel F N) X (f₁ + f₂) =
      rightDerivative (matrixModel F N) X f₁ + rightDerivative (matrixModel F N) X f₂ := by
  funext g
  rw [Pi.add_apply, rightDerivative_eq_fderiv_mul_left hf₁, rightDerivative_eq_fderiv_mul_left hf₂,
    rightDerivative_eq_fderiv_mul_left (hf₁.add hf₂)]
  have hfun : (fun y : Matrix (Fin N) (Fin N) F =>
      unitsExtension (f₁ + f₂) ((g : Matrix (Fin N) (Fin N) F) * y)) =
      (fun y => unitsExtension f₁ ((g : Matrix (Fin N) (Fin N) F) * y)) +
        fun y => unitsExtension f₂ ((g : Matrix (Fin N) (Fin N) F) * y) :=
    funext fun y => unitsExtension_add f₁ f₂ _
  rw [hfun, ((differentiableAt_unitsExtension_mul_left hf₁ g).hasFDerivAt.add
    (differentiableAt_unitsExtension_mul_left hf₂ g).hasFDerivAt).fderiv]
  rfl

theorem rightDerivative_smul {f : Langlands.GeneralLinear N F → ℂ}
    (hf : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f) (c : ℂ) (X : Matrix (Fin N) (Fin N) F) :
    rightDerivative (matrixModel F N) X (c • f) = c • rightDerivative (matrixModel F N) X f := by
  have hcf : ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ (c • f) :=
    ((c • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hf
  funext g
  rw [Pi.smul_apply, rightDerivative_eq_fderiv_mul_left hf, rightDerivative_eq_fderiv_mul_left hcf]
  have hfun : (fun y : Matrix (Fin N) (Fin N) F =>
      unitsExtension (c • f) ((g : Matrix (Fin N) (Fin N) F) * y)) =
      fun y => c * unitsExtension f ((g : Matrix (Fin N) (Fin N) F) * y) :=
    funext fun y => unitsExtension_smul c f _
  rw [hfun, fderiv_const_mul (differentiableAt_unitsExtension_mul_left hf g)]
  rfl

/-- The right derivative is real-linear in the direction. -/
theorem rightDerivative_sum_smul {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (Y : ι → Matrix (Fin N) (Fin N) F) (f : Langlands.GeneralLinear N F → ℂ) :
    rightDerivative (matrixModel F N) (∑ i ∈ s, r i • Y i) f =
      ∑ i ∈ s, r i • rightDerivative (matrixModel F N) (Y i) f := by
  funext g
  simp only [rightDerivative, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]

/-- The right derivative along `X` as a complex-linear map on a space of smooth functions. -/
def rightDerivativeLinearMap (V : Submodule ℂ (Langlands.GeneralLinear N F → ℂ))
    (hV : ∀ f ∈ V, ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f) (X : Matrix (Fin N) (Fin N) F) :
    V →ₗ[ℂ] (Langlands.GeneralLinear N F → ℂ) where
  toFun f := rightDerivative (matrixModel F N) X f
  map_add' f₁ f₂ := rightDerivative_add (hV _ f₁.2) (hV _ f₂.2) X
  map_smul' c f := rightDerivative_smul (hV _ f.2) c X

/-! ## `K`-finiteness -/

/-- Right translation by an element of `K` preserves the `K`-finite functions of a space of
functions stable under right translation by `K`. -/
theorem rightTranslation_mem_kFiniteFunctions (V : Submodule ℂ (Langlands.GeneralLinear N F → ℂ))
    (K : Subgroup (Langlands.GeneralLinear N F))
    (hVK : ∀ k ∈ K, ∀ f ∈ V, Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) k f ∈ V)
    {f : Langlands.GeneralLinear N F → ℂ} (hf : f ∈ kFiniteFunctions V K)
    {k : Langlands.GeneralLinear N F} (hk : k ∈ K) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) k f ∈ kFiniteFunctions V K := by
  refine ⟨hVK k hk f hf.1, (mem_kFiniteVectors_iff _ _ _).mpr ?_⟩
  have hfK := (mem_kFiniteVectors_iff _ _ _).mp hf.2
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.mpr ?_ :
    _ ≤ Submodule.span ℂ (Set.range fun k' : K =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) (k' : _) f))
  rintro _ ⟨k', rfl⟩
  refine Submodule.subset_span ⟨k' * ⟨k, hk⟩, ?_⟩
  change Whittaker.rightTranslation ℂ _ ((k' : _) * k) f = _
  rw [map_mul]
  rfl

/-- The right derivative of a `K`-finite function in a space of smooth functions stable under
right translation by `K` is `K`-finite. -/
theorem rightDerivative_mem_kFiniteVectors (V : Submodule ℂ (Langlands.GeneralLinear N F → ℂ))
    (K : Subgroup (Langlands.GeneralLinear N F))
    (hV : ∀ f ∈ V, ContMDiff (matrixModel F N) 𝓘(ℝ, ℂ) ∞ f)
    (hVK : ∀ k ∈ K, ∀ f ∈ V, Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) k f ∈ V)
    {f : Langlands.GeneralLinear N F → ℂ} (hf : f ∈ kFiniteFunctions V K)
    (X : Matrix (Fin N) (Fin N) F) :
    rightDerivative (matrixModel F N) X f ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F)) K := by
  obtain ⟨hfV, hfK⟩ := hf
  replace hfK := (mem_kFiniteVectors_iff _ _ _).mp hfK
  rw [mem_kFiniteVectors_iff]
  set W := Submodule.span ℂ (Set.range fun k : K =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) (k : _) f) with hW
  have hWV : W ≤ V := Submodule.span_le.mpr (by
    rintro _ ⟨k, rfl⟩
    exact hVK k k.2 f hfV)
  let b := Module.finBasis ℝ (Matrix (Fin N) (Fin N) F)
  let T : Fin (Module.finrank ℝ (Matrix (Fin N) (Fin N) F)) →
      W →ₗ[ℂ] (Langlands.GeneralLinear N F → ℂ) :=
    fun i => (rightDerivativeLinearMap V hV (b i)).comp (Submodule.inclusion hWV)
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.mpr ?_ :
    _ ≤ ⨆ i, LinearMap.range (T i))
  rintro _ ⟨k, rfl⟩
  have hw : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) (k : _) f ∈ W :=
    Submodule.subset_span ⟨k, rfl⟩
  change Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) (k : _)
    (rightDerivative (matrixModel F N) X f) ∈ _
  rw [rightTranslation_rightDerivative (hV f hfV), ← b.sum_repr
    (((k : Langlands.GeneralLinear N F) : Matrix (Fin N) (Fin N) F) * X *
      (((k : Langlands.GeneralLinear N F)⁻¹ : Langlands.GeneralLinear N F) :
        Matrix (Fin N) (Fin N) F)), rightDerivative_sum_smul]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ ?_
  exact Submodule.mem_iSup_of_mem i ⟨⟨_, hw⟩, rfl⟩

/-! ## Principal series -/

variable (χ : ℕ → Fˣ → ℂ)

/-- The principal series is stable under right translation by all of `GL_N(F)`. -/
theorem rightTranslation_mem_principalSeries {f : Langlands.GeneralLinear N F → ℂ}
    (hf : f ∈ principalSeries F N χ) (s : Langlands.GeneralLinear N F) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) s f ∈ principalSeries F N χ := by
  refine ⟨hf.1.comp contMDiff_mul_right, fun a u g => ?_⟩
  change f (_ * _ * g * s) = _ * f (g * s)
  rw [mul_assoc _ g s, hf.2]

/-- The principal series is stable under right derivatives. -/
theorem rightDerivative_mem_principalSeries {f : Langlands.GeneralLinear N F → ℂ}
    (hf : f ∈ principalSeries F N χ) (X : Matrix (Fin N) (Fin N) F) :
    rightDerivative (matrixModel F N) X f ∈ principalSeries F N χ :=
  ⟨contMDiff_rightDerivative hf.1 X, fun a u g =>
    rightDerivative_mul_left_of_eq hf.1 (fun g' => hf.2 a u g') X g⟩

/-- The `K`-finite functions of the principal series are stable under right translation by
`K`. -/
theorem rightTranslation_mem_kFiniteFunctions_principalSeries
    (K : Subgroup (Langlands.GeneralLinear N F)) {f : Langlands.GeneralLinear N F → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries F N χ) K) {k : Langlands.GeneralLinear N F}
    (hk : k ∈ K) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N F) k f ∈
      kFiniteFunctions (principalSeries F N χ) K :=
  rightTranslation_mem_kFiniteFunctions _ K
    (fun k _ _ hf => rightTranslation_mem_principalSeries χ hf k) hf hk

/-- The `K`-finite functions of the principal series are stable under right derivatives. -/
theorem rightDerivative_mem_kFiniteFunctions_principalSeries
    (K : Subgroup (Langlands.GeneralLinear N F)) {f : Langlands.GeneralLinear N F → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries F N χ) K) (X : Matrix (Fin N) (Fin N) F) :
    rightDerivative (matrixModel F N) X f ∈ kFiniteFunctions (principalSeries F N χ) K :=
  ⟨rightDerivative_mem_principalSeries χ hf.1 X,
    rightDerivative_mem_kFiniteVectors _ K
      (fun g (hg : g ∈ principalSeries F N χ) => hg.1)
      (fun k _ _ hf => rightTranslation_mem_principalSeries χ hf k) hf X⟩

/-! ## The complex standard modules -/

/-- The `K`-finite functions of a complex standard module are stable under right translation
by `U(n)`. -/
theorem rightTranslation_mem_kFiniteFunctions_complexStandardModule (n : ℕ)
    (ds : List ComplexCharacterData) {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))
    {k : Langlands.GeneralLinear n ℂ} (hk : k ∈ unitaryCompact ℂ n) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k f ∈
      kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) :=
  rightTranslation_mem_kFiniteFunctions_principalSeries _ _ hf hk

/-- The `K`-finite functions of a complex standard module are stable under right derivatives
along `𝔤𝔩_n(ℂ)`. -/
theorem rightDerivative_mem_kFiniteFunctions_complexStandardModule (n : ℕ)
    (ds : List ComplexCharacterData) {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))
    (X : Matrix (Fin n) (Fin n) ℂ) :
    rightDerivative (matrixModel ℂ n) X f ∈
      kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) :=
  rightDerivative_mem_kFiniteFunctions_principalSeries _ _ hf X

end Langlands.Archimedean
