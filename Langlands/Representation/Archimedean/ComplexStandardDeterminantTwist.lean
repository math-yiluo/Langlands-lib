import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Langlands.Representation.Archimedean.ComplexTemperedComplement
import Langlands.LocalFactor.ArchimedeanPairFactor
import Langlands.Global.ArchimedeanCharacterSmoothness

/-!
# Twisting complex principal series by a character of the determinant

For a continuous character `η` of `ℂˣ`, multiplication by `g ↦ η(det g)` carries the smooth
principal series of the characters `χ_i` of `GL_n(ℂ)` to that of the characters `χ_i η`, and
its `U(n)`-finite functions to `U(n)`-finite functions. It conjugates right translation by
`k` to `η(det k)` times right translation, and the right derivative along `X` to the right
derivative plus the derivative of `η ∘ det` at `1` along `X`. For a list of complex character
blocks, the characters of the list multiplied by `d` are those of the list times `d`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexDeterminantTwist

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

variable {n : ℕ}

/-- The function `g ↦ η(det g)` on `GL_n(ℂ)`, for a continuous character `η` of `ℂˣ`. -/
def detCharacter (η : ℂˣ →ₜ* ℂˣ) (g : Langlands.GeneralLinear n ℂ) : ℂ :=
  (η (GeneralLinear.determinant g) : ℂ)

theorem detCharacter_mul (η : ℂˣ →ₜ* ℂˣ) (g h : Langlands.GeneralLinear n ℂ) :
    detCharacter η (g * h) = detCharacter η g * detCharacter η h := by
  simp only [detCharacter, map_mul, Units.val_mul]

theorem detCharacter_one (η : ℂˣ →ₜ* ℂˣ) :
    detCharacter η (1 : Langlands.GeneralLinear n ℂ) = 1 := by
  simp only [detCharacter, map_one, Units.val_one]

theorem detCharacter_ne_zero (η : ℂˣ →ₜ* ℂˣ) (g : Langlands.GeneralLinear n ℂ) :
    detCharacter η g ≠ 0 :=
  Units.ne_zero _

/-- The inverse character gives the pointwise inverse function. -/
theorem detCharacter_inv (η : ℂˣ →ₜ* ℂˣ) (g : Langlands.GeneralLinear n ℂ) :
    detCharacter η⁻¹ g = (detCharacter η g)⁻¹ :=
  Units.val_inv_eq_inv_val _

theorem detCharacter_inv_mul (η : ℂˣ →ₜ* ℂˣ) (g : Langlands.GeneralLinear n ℂ) :
    detCharacter η⁻¹ g * detCharacter η g = 1 := by
  rw [detCharacter_inv, inv_mul_cancel₀ (detCharacter_ne_zero η g)]

/-- `η ∘ det` is smooth on `GL_n(ℂ)`. -/
theorem contMDiff_detCharacter (η : ℂˣ →ₜ* ℂˣ) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (detCharacter (n := n) η) := by
  refine contMDiff_of_contDiffOn (ψ := fun Y : Matrix (Fin n) (Fin n) ℂ =>
    Langlands.Global.unitsCharacterExtension η Y.det) ?_ fun g => ?_
  · intro Y hY
    have hY' : IsUnit Y := hY
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det Y).mp hY'
    have hd := Langlands.Global.contDiffAt_unitsCharacterExtension η u
    rw [hu] at hd
    exact (hd.comp Y ComplexMaximalParabolicIntegration.contDiff_det.contDiffAt).contDiffWithinAt
  · change (η (GeneralLinear.determinant g) : ℂ) = _
    rw [← Langlands.Global.unitsCharacterExtension_unit η (GeneralLinear.determinant g),
      Matrix.GeneralLinearGroup.val_det_apply]

/-- The determinant of an upper unipotent matrix is one. -/
theorem determinant_upperUnipotent (u : upperUnipotent n ℂ) :
    GeneralLinear.determinant (u : Langlands.GeneralLinear n ℂ) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact ComplexMaximalParabolicIntegration.det_upperUnipotent u

/-- The determinant of a diagonal matrix of units is the product of the units. -/
theorem determinant_diagonalUnits (a : Fin n → ℂˣ) :
    GeneralLinear.determinant (Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) =
      ∏ i, a i := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Iwasawa.diagonalUnits_val,
    Matrix.det_diagonal, Units.coe_prod]

/-- On the Borel subgroup, `η ∘ det` is `η` of the product of the diagonal entries. -/
theorem detCharacter_borel (η : ℂˣ →ₜ* ℂˣ) (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    detCharacter η ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) * g) =
      (∏ i, (η (a i) : ℂ)) * detCharacter η g := by
  rw [detCharacter_mul, detCharacter_mul]
  have hu : detCharacter η (u : Langlands.GeneralLinear n ℂ) = 1 := by
    rw [detCharacter, determinant_upperUnipotent, map_one, Units.val_one]
  rw [hu, mul_one, detCharacter, determinant_diagonalUnits, map_prod, Units.coe_prod]

/-- Twisting the characters of a principal series by `η` multiplies its character by `η` of
the product of the diagonal entries. -/
theorem principalSeriesCharacter_twist (η : ℂˣ →ₜ* ℂˣ) {χ χ' : ℕ → ℂˣ → ℂ}
    (h : ∀ (i : Fin n) (z : ℂˣ), χ' i z = χ i z * (η z : ℂ)) (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n χ' a =
      principalSeriesCharacter ℂ n χ a * ∏ i, (η (a i) : ℂ) := by
  unfold principalSeriesCharacter
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [h]
  ring

/-- Multiplication by `η ∘ det` maps the principal series of `χ` to that of `χ η`. -/
theorem detCharacter_mul_mem_principalSeries (η : ℂˣ →ₜ* ℂˣ) {χ χ' : ℕ → ℂˣ → ℂ}
    (h : ∀ (i : Fin n) (z : ℂˣ), χ' i z = χ i z * (η z : ℂ))
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ principalSeries ℂ n χ) :
    (fun g => detCharacter η g * f g) ∈ principalSeries ℂ n χ' := by
  refine ⟨ComplexJacquetLimit.contMDiff_mul_fun (contMDiff_detCharacter η) hf.1,
    fun a u g => ?_⟩
  change detCharacter η (_ * _ * g) * f (_ * _ * g) = _ * (detCharacter η g * f g)
  rw [detCharacter_borel, hf.2 a u g, principalSeriesCharacter_twist η h]
  ring

/-- Multiplication by `η ∘ det`, as a linear map on functions on `GL_n(ℂ)`. -/
def detMul (η : ℂˣ →ₜ* ℂˣ) :
    (Langlands.GeneralLinear n ℂ → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear n ℂ → ℂ) where
  toFun f g := detCharacter η g * f g
  map_add' f h := by
    funext g
    exact mul_add _ _ _
  map_smul' c f := by
    funext g
    exact mul_left_comm _ _ _

@[simp]
theorem detMul_apply (η : ℂˣ →ₜ* ℂˣ) (f : Langlands.GeneralLinear n ℂ → ℂ)
    (g : Langlands.GeneralLinear n ℂ) : detMul η f g = detCharacter η g * f g :=
  rfl

/-- Right translation by `k` of a multiplied function is `η(det k)` times the multiplied
translate. -/
theorem rightTranslation_detMul (η : ℂˣ →ₜ* ℂˣ) (k : Langlands.GeneralLinear n ℂ)
    (f : Langlands.GeneralLinear n ℂ → ℂ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k (detMul η f) =
      detCharacter η k •
        detMul η (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k f) := by
  funext g
  change detCharacter η (g * k) * f (g * k) = detCharacter η k * (detCharacter η g * f (g * k))
  rw [detCharacter_mul]
  ring

/-- Multiplication by `η ∘ det` preserves `K`-finiteness for right translation. -/
theorem detMul_mem_kFiniteVectors (η : ℂˣ →ₜ* ℂˣ) (K : Subgroup (Langlands.GeneralLinear n ℂ))
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)) K) :
    detMul η f ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)) K := by
  rw [mem_kFiniteVectors_iff] at hf ⊢
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.mpr ?_ :
    _ ≤ (Submodule.span ℂ (Set.range fun k : K =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (k : _) f)).map (detMul η))
  rintro _ ⟨k, rfl⟩
  change Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (k : _) (detMul η f) ∈ _
  rw [rightTranslation_detMul]
  exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩))

/-- Multiplication by `η ∘ det` maps the `U(n)`-finite functions of the principal series of
`χ` to those of the principal series of `χ η`. -/
theorem detMul_mem_kFiniteFunctions (η : ℂˣ →ₜ* ℂˣ) {χ χ' : ℕ → ℂˣ → ℂ}
    (h : ∀ (i : Fin n) (z : ℂˣ), χ' i z = χ i z * (η z : ℂ))
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) :
    detMul η f ∈ kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n) :=
  ⟨detCharacter_mul_mem_principalSeries η h hf.1, detMul_mem_kFiniteVectors η _ hf.2⟩

/-- Multiplication by `η ∘ det` between `U(n)`-finite principal-series functions. -/
def kFiniteDetMul (η : ℂˣ →ₜ* ℂˣ) {χ χ' : ℕ → ℂˣ → ℂ}
    (h : ∀ (i : Fin n) (z : ℂˣ), χ' i z = χ i z * (η z : ℂ)) :
    kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n) :=
  (detMul η).restrict fun _ hf => detMul_mem_kFiniteFunctions η h hf

theorem coe_kFiniteDetMul (η : ℂˣ →ₜ* ℂˣ) {χ χ' : ℕ → ℂˣ → ℂ}
    (h : ∀ (i : Fin n) (z : ℂˣ), χ' i z = χ i z * (η z : ℂ))
    (f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) :
    ((kFiniteDetMul η h f : kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n)) :
      Langlands.GeneralLinear n ℂ → ℂ) = detMul η f :=
  LinearMap.coe_restrict_apply _ f

theorem kFiniteDetMul_injective (η : ℂˣ →ₜ* ℂˣ) {χ χ' : ℕ → ℂˣ → ℂ}
    (h : ∀ (i : Fin n) (z : ℂˣ), χ' i z = χ i z * (η z : ℂ)) :
    Function.Injective (kFiniteDetMul η h) := by
  intro f₁ f₂ hf
  apply Subtype.ext
  funext g
  have hg := congrFun (congrArg Subtype.val hf) g
  rw [coe_kFiniteDetMul, coe_kFiniteDetMul, detMul_apply, detMul_apply] at hg
  exact mul_left_cancel₀ (detCharacter_ne_zero η g) hg

/-- The Leibniz rule for multiplication by `η ∘ det`: the right derivative of `η(det) f` is
`η(det)` times the derivative of `f` plus the derivative of `η ∘ det` at `1` times `f`. -/
theorem rightDerivative_detMul (η : ℂˣ →ₜ* ℂˣ) {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f) (X : Matrix (Fin n) (Fin n) ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    rightDerivative (matrixModel ℂ n) X (detMul η f) g =
      detCharacter η g *
        (rightDerivative (matrixModel ℂ n) X (detCharacter (n := n) η) 1 * f g +
          rightDerivative (matrixModel ℂ n) X f g) := by
  have h1 := ComplexTemperedComplement.rightDerivative_mul_fun (contMDiff_detCharacter η) hf X g
  have h2 := rightDerivative_mul_left_of_eq (F := ℂ) (N := n) (contMDiff_detCharacter η)
    (a := g) (c := detCharacter η g) (fun h => detCharacter_mul η g h) X 1
  rw [mul_one] at h2
  change rightDerivative (matrixModel ℂ n) X (fun g => detCharacter η g * f g) g = _
  rw [h1, h2]
  ring

/-! ## Lists of complex character blocks -/

/-- Multiplying every block by `d` multiplies every position character inside the list by
the character of `d`. -/
theorem complexPositionCharacter_map_mul (d : ComplexCharacterData) :
    ∀ (ds : List ComplexCharacterData) (i : ℕ), i < ds.length → ∀ z : ℂˣ,
      complexPositionCharacter (ds.map fun e => e.mul d) i z =
        complexPositionCharacter ds i z * (d.character z : ℂ)
  | [], i, hi, _ => by simp at hi
  | e :: ds, 0, _, z => by
      simp [complexPositionCharacter, ComplexCharacterData.mul]
  | e :: ds, i + 1, hi, z => by
      simpa [complexPositionCharacter] using
        complexPositionCharacter_map_mul d ds i (by simpa using hi) z

/-- Dividing by the character of `d` recovers the position characters of `ds` from those of
the list with every block multiplied by `d`. -/
theorem complexPositionCharacter_map_mul_inv (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) (hr : ds.length = n) (i : Fin n) (z : ℂˣ) :
    complexPositionCharacter ds i z =
      complexPositionCharacter (ds.map fun e => e.mul d) i z * ((d.character⁻¹ z : ℂˣ) : ℂ) := by
  rw [complexPositionCharacter_map_mul d ds i (by rw [hr]; exact i.2) z, mul_assoc,
    ← Units.val_mul]
  change _ = _ * ((d.character z * (d.character z)⁻¹ : ℂˣ) : ℂ)
  rw [mul_inv_cancel, Units.val_one, mul_one]

/-- The derivative at `1` of `η⁻¹ ∘ det` is minus that of `η ∘ det`. -/
theorem rightDerivative_detCharacter_inv (η : ℂˣ →ₜ* ℂˣ) (X : Matrix (Fin n) (Fin n) ℂ) :
    rightDerivative (matrixModel ℂ n) X (detCharacter (n := n) η⁻¹) 1 =
      -rightDerivative (matrixModel ℂ n) X (detCharacter (n := n) η) 1 := by
  have h := ComplexTemperedComplement.rightDerivative_mul_fun (contMDiff_detCharacter (n := n) η⁻¹)
    (contMDiff_detCharacter η) X 1
  have hconst : (fun g : Langlands.GeneralLinear n ℂ => detCharacter η⁻¹ g * detCharacter η g) =
      fun _ => (1 : ℂ) := funext fun g => detCharacter_inv_mul η g
  have hzero : rightDerivative (matrixModel ℂ n) X (fun _ : Langlands.GeneralLinear n ℂ => (1 : ℂ))
      1 = 0 := by
    simp only [rightDerivative, mfderiv_const]
    rfl
  rw [hconst, hzero, detCharacter_one, detCharacter_one, mul_one, one_mul] at h
  linear_combination -h

/-- Multiplication by `η ∘ det` conjugates right translation by `k ∈ U(n)` to `η(det k)⁻¹`
times right translation. -/
theorem kFiniteDetMul_rightTranslation (η : ℂˣ →ₜ* ℂˣ) {χ χ' : ℕ → ℂˣ → ℂ}
    (h : ∀ (i : Fin n) (z : ℂˣ), χ' i z = χ i z * (η z : ℂ))
    (f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    {k : Langlands.GeneralLinear n ℂ} (hk : k ∈ unitaryCompact ℂ n) :
    kFiniteDetMul η h
        ⟨_, rightTranslation_mem_kFiniteFunctions_principalSeries χ (unitaryCompact ℂ n) f.2 hk⟩ =
      (detCharacter η k)⁻¹ •
        ⟨_, rightTranslation_mem_kFiniteFunctions_principalSeries χ' (unitaryCompact ℂ n)
          (kFiniteDetMul η h f).2 hk⟩ := by
  apply Subtype.ext
  funext g
  rw [coe_kFiniteDetMul]
  change detCharacter η g * f.val (g * k) =
    (detCharacter η k)⁻¹ * (kFiniteDetMul η h f).val (g * k)
  rw [coe_kFiniteDetMul, detMul_apply, detCharacter_mul]
  have hk0 := detCharacter_ne_zero η k
  field_simp

/-- Multiplication by `η ∘ det` conjugates the right derivative along `X` to the right
derivative minus the derivative of `η ∘ det` at `1` along `X`, written as the sum with the
negated derivative. -/
theorem kFiniteDetMul_rightDerivative (η : ℂˣ →ₜ* ℂˣ) {χ χ' : ℕ → ℂˣ → ℂ}
    (h : ∀ (i : Fin n) (z : ℂˣ), χ' i z = χ i z * (η z : ℂ))
    (f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (X : Matrix (Fin n) (Fin n) ℂ) :
    kFiniteDetMul η h
        ⟨_, rightDerivative_mem_kFiniteFunctions_principalSeries χ (unitaryCompact ℂ n) f.2 X⟩ =
      ⟨_, rightDerivative_mem_kFiniteFunctions_principalSeries χ' (unitaryCompact ℂ n)
          (kFiniteDetMul η h f).2 X⟩ +
        (-rightDerivative (matrixModel ℂ n) X (detCharacter (n := n) η) 1) •
          kFiniteDetMul η h f := by
  apply Subtype.ext
  funext g
  have hsmooth : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f.val := f.2.1.1
  rw [coe_kFiniteDetMul]
  change detCharacter η g * rightDerivative (matrixModel ℂ n) X f.val g =
    rightDerivative (matrixModel ℂ n) X (kFiniteDetMul η h f).val g +
      -rightDerivative (matrixModel ℂ n) X (detCharacter (n := n) η) 1 *
        (kFiniteDetMul η h f).val g
  rw [coe_kFiniteDetMul, rightDerivative_detMul η hsmooth X g, detMul_apply]
  ring

end Langlands.Archimedean.ComplexDeterminantTwist
