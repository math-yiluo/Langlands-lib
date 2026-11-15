import Langlands.Representation.Archimedean.JacquetLimit

/-!
# Submodules of the dual principal series and the Jacquet integral in stages
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace JacquetDual

open MaximalParabolicIntegration ParabolicChartBound PartialJacquet JacquetLimit GramFormula
  Langlands.GeneralLinear RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

local instance borelSpaceK_jd (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

/-- The Jacquet integral `Λ_n`, computed in stages along the maximal parabolic subgroups:
`Λ_0(h) = h(1)` and `Λ_{m+1}(h) = Λ_m(T h)`. -/
def jacquet : (n : ℕ) → (Langlands.GeneralLinear n ℝ → ℂ) → ℂ
  | 0, h => h 1
  | m + 1, h => jacquet m (jacquetStep h)

variable {m : ℕ} {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-! ## Restriction to the Levi factor -/

/-- The restriction `u ↦ u ∘ ι` to `GL_m(ℝ)`, embedded as `g ↦ diag(g, 1)`. -/
def restrictLevi :
    (Langlands.GeneralLinear (m + 1) ℝ → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear m ℝ → ℂ) where
  toFun u g := u (iotaGL g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrictLevi_apply (u : Langlands.GeneralLinear (m + 1) ℝ → ℂ)
    (g : Langlands.GeneralLinear m ℝ) : restrictLevi u g = u (iotaGL g) := rfl

theorem contMDiff_restrictLevi {u : Langlands.GeneralLinear (m + 1) ℝ → ℂ}
    (hu : ContMDiff (matrixModel ℝ (m + 1)) 𝓘(ℝ, ℂ) ∞ u) :
    ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ (restrictLevi u) := by
  refine contMDiff_of_contDiffOn (ψ := fun Y => unitsExtension u (iota Y)) ?_ fun g => ?_
  · intro Y hY
    have hY' : IsUnit Y := hY
    have hunit : IsUnit (iota Y) := by
      rw [Matrix.isUnit_iff_isUnit_det, det_iota]
      exact (Matrix.isUnit_iff_isUnit_det Y).mp hY'
    exact (((contDiffOn_unitsExtension hu).contDiffAt
      (isOpen_setOf_isUnit_matrix.mem_nhds hunit)).comp Y
        contDiff_iota.contDiffAt).contDiffWithinAt
  · rw [restrictLevi_apply, ← iotaGL_val, unitsExtension_val]

theorem principalSeriesCharacter_lastCases_dual (hχ : IsSignedPower χ e) (a : Fin m → ℝˣ) :
    principalSeriesCharacter ℝ (m + 1) (dualChar χ) (fun i => Fin.lastCases 1 a i) =
      principalSeriesCharacter ℝ m (dualChar (shiftChar χ)) a := by
  rw [principalSeriesCharacter, principalSeriesCharacter, Fin.prod_univ_castSucc]
  simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_castSucc, Fin.val_last,
    dualChar, hχ.one, inv_one, Units.val_one, norm_one, one_pow, Complex.ofReal_one,
    Complex.one_cpow, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [shiftChar]
  simp only [Module.finrank_self, pow_one, Real.norm_eq_abs]
  have hx : ((|(a i : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr (a i).ne_zero
  rw [mul_inv, ← Complex.cpow_neg, neg_neg, mul_assoc, ← Complex.cpow_add _ _ hx]
  congr 2
  push_cast
  ring

theorem restrictLevi_mem (hχ : IsSignedPower χ e) {u : Langlands.GeneralLinear (m + 1) ℝ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℝ (m + 1) (dualChar χ))
      (unitaryCompact ℝ (m + 1))) :
    restrictLevi u ∈ kFiniteFunctions (principalSeries ℝ m (dualChar (shiftChar χ)))
      (unitaryCompact ℝ m) := by
  refine ⟨⟨contMDiff_restrictLevi hu.1.1, fun a v g => ?_⟩, ?_⟩
  · rw [restrictLevi_apply, restrictLevi_apply, map_mul, map_mul, iotaGL_diagonalUnits]
    have := hu.1.2 (fun i => Fin.lastCases 1 a i)
      ⟨iotaGL (v : Langlands.GeneralLinear m ℝ), iotaGL_mem_upperUnipotent v⟩ (iotaGL g)
    rw [this, principalSeriesCharacter_lastCases_dual hχ]
  · refine (mem_kFiniteVectors_iff _ _ _).mpr ?_
    have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ (m + 1) =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (m + 1) ℝ)
          (k : Langlands.GeneralLinear (m + 1) ℝ) u)) := (mem_kFiniteVectors_iff _ _ _).mp hu.2
    have hle : Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ m =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear m ℝ)
          (k : Langlands.GeneralLinear m ℝ) (restrictLevi u)) ≤
        (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ (m + 1) =>
          Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (m + 1) ℝ)
            (k : Langlands.GeneralLinear (m + 1) ℝ) u)).map restrictLevi := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      refine ⟨_, Submodule.subset_span ⟨⟨iotaGL (k : Langlands.GeneralLinear m ℝ),
        iotaGL_mem_unitaryCompact k.2⟩, rfl⟩, funext fun g => ?_⟩
      change u (iotaGL g * iotaGL (k : Langlands.GeneralLinear m ℝ)) =
        u (iotaGL (g * (k : Langlands.GeneralLinear m ℝ)))
      rw [map_mul]
    exact Submodule.finiteDimensional_of_le hle

theorem rightTranslation_restrictLevi (u : Langlands.GeneralLinear (m + 1) ℝ → ℂ)
    (k : Langlands.GeneralLinear m ℝ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear m ℝ) k (restrictLevi u) =
      restrictLevi (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (m + 1) ℝ)
        (iotaGL k) u) := by
  funext g
  change u (iotaGL (g * k)) = u (iotaGL g * iotaGL k)
  rw [map_mul]

theorem hasFDerivAt_iota :
    HasFDerivAt (iota (m := m)) (LinearMap.toContinuousLinearMap (iotaLin (m := m))) 1 := by
  have h : iota (m := m) = fun Y => LinearMap.toContinuousLinearMap iotaLin Y + iota 0 :=
    funext fun Y => by rw [iota_eq_iotaLin_add]; rfl
  rw [h]
  exact (LinearMap.toContinuousLinearMap iotaLin).hasFDerivAt.add_const _

theorem rightDerivative_restrictLevi {u : Langlands.GeneralLinear (m + 1) ℝ → ℂ}
    (hu : ContMDiff (matrixModel ℝ (m + 1)) 𝓘(ℝ, ℂ) ∞ u) (Y : Matrix (Fin m) (Fin m) ℝ) :
    rightDerivative (matrixModel ℝ m) Y (restrictLevi u) =
      restrictLevi (rightDerivative (matrixModel ℝ (m + 1)) (iotaLin Y) u) := by
  funext g
  rw [restrictLevi_apply, rightDerivative_eq_fderiv_mul_left (contMDiff_restrictLevi hu),
    rightDerivative_eq_fderiv_mul_left hu]
  set Φ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ → ℂ := fun z =>
    unitsExtension u (((iotaGL g : Langlands.GeneralLinear (m + 1) ℝ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * z) with hΦ
  have hev : (fun y : Matrix (Fin m) (Fin m) ℝ =>
      unitsExtension (restrictLevi u) ((g : Matrix (Fin m) (Fin m) ℝ) * y)) =ᶠ[𝓝 1]
      Φ ∘ iota := by
    filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds
      (isUnit_one : IsUnit (1 : Matrix (Fin m) (Fin m) ℝ))] with y hy
    have hy' : IsUnit y := hy
    have h1 : (g : Matrix (Fin m) (Fin m) ℝ) * y =
        ((g * hy'.unit : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) := by
      rw [Units.val_mul, IsUnit.unit_spec]
    have h2 : ((iotaGL g : Langlands.GeneralLinear (m + 1) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * iota y =
        ((iotaGL (g * hy'.unit) : Langlands.GeneralLinear (m + 1) ℝ) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) := by
      rw [map_mul, Units.val_mul, iotaGL_val, iotaGL_val, IsUnit.unit_spec]
    simp only [Function.comp_apply, hΦ]
    rw [h1, unitsExtension_val, h2, unitsExtension_val, restrictLevi_apply]
  rw [hev.fderiv_eq]
  have hΦd : DifferentiableAt ℝ Φ (iota 1) := by
    rw [iota_one]
    exact differentiableAt_unitsExtension_mul_left hu (iotaGL g)
  rw [fderiv_comp _ hΦd hasFDerivAt_iota.differentiableAt, hasFDerivAt_iota.fderiv, iota_one]
  rfl

/-! ## The restricted submodule -/

theorem map_restrictLevi_ne_bot {U : Submodule ℂ (Langlands.GeneralLinear (m + 1) ℝ → ℂ)}
    (hU : U ≤ kFiniteFunctions (principalSeries ℝ (m + 1) (dualChar χ))
      (unitaryCompact ℝ (m + 1)))
    (hUK : ∀ k ∈ unitaryCompact ℝ (m + 1), ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (m + 1) ℝ) k u ∈ U)
    (hU0 : U ≠ ⊥) : U.map restrictLevi ≠ ⊥ := by
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  obtain ⟨κ, hκ, hκ0⟩ : ∃ κ ∈ unitaryCompact ℝ (m + 1), u κ ≠ 0 := by
    by_contra hcon
    exact hu0 (eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact (hU huU).1
      fun k hk => by_contra fun h => hcon ⟨k, hk, h⟩)
  intro hbot
  have hmem : restrictLevi (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (m + 1) ℝ) κ u) ∈
      U.map restrictLevi := ⟨_, hUK κ hκ u huU, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  have := congrFun hmem 1
  change u (iotaGL 1 * κ) = 0 at this
  rw [map_one, one_mul] at this
  exact hκ0 this

/-! ## Orthogonality invariance with the normalized Haar measure -/

/-- The identification of `O(n) ⊆ GL_n(ℝ)` with the matrix unitary group. -/
def toUnitaryGroup (n : ℕ) (k : unitaryCompact ℝ n) : Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩

theorem continuous_toUnitaryGroup (n : ℕ) : Continuous (toUnitaryGroup n) :=
  Continuous.subtype_mk (Units.continuous_val.comp continuous_subtype_val) _

theorem integral_map_toUnitaryGroup {n : ℕ} {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : Continuous f) :
    ∫ κ, f (Unitary.toUnits κ) ∂((haarK n).map (toUnitaryGroup n)) =
      ∫ k, f (k : Langlands.GeneralLinear n ℝ) ∂haarK n := by
  rw [integral_map (f := fun κ : Matrix.unitaryGroup (Fin n) ℝ => f (Unitary.toUnits κ))
    (continuous_toUnitaryGroup n).measurable.aemeasurable
    (hf.comp continuous_unitary_toUnits).aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  have hk : Unitary.toUnits (toUnitaryGroup n k) = (k : Langlands.GeneralLinear n ℝ) :=
    Units.ext rfl
  change f (Unitary.toUnits (toUnitaryGroup n k)) = f (k : Langlands.GeneralLinear n ℝ)
  rw [hk]

theorem integral_mul_eq_zero_of_orthogonal {n : ℕ} (hχ : IsSignedPower χ e)
    {U : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)}
    (hU : U ≤ kFiniteFunctions (principalSeries ℝ n (dualChar χ)) (unitaryCompact ℝ n))
    (hUK : ∀ k ∈ unitaryCompact ℝ n, ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k u ∈ U)
    (hUD : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ u ∈ U, rightDerivative (matrixModel ℝ n) X u ∈ U)
    {h : Langlands.GeneralLinear n ℝ → ℂ} (hh : Continuous h)
    (horth : ∀ u ∈ U, ∫ k, u (k : Langlands.GeneralLinear n ℝ) * h k ∂haarK n = 0) :
    ∀ u ∈ U, ∀ g : Langlands.GeneralLinear n ℝ,
      ∫ k, u ((k : Langlands.GeneralLinear n ℝ) * g) * h k ∂haarK n = 0 := by
  intro u hu g
  set μ := (haarK n).map (toUnitaryGroup n)
  have hφ : Continuous fun κ : Matrix.unitaryGroup (Fin n) ℝ => h (Unitary.toUnits κ) :=
    hh.comp continuous_unitary_toUnits
  have hcont : ∀ w ∈ U, ∀ g : Langlands.GeneralLinear n ℝ,
      Continuous fun y : Langlands.GeneralLinear n ℝ => w (y * g) * h y := fun w hw g =>
    ((hU hw).1.1.continuous.comp (continuous_id.mul continuous_const)).mul hh
  have h1 : ∀ w ∈ U, MatrixCoefficientAnalytic.matrixCoefficient μ w
      (fun κ => h (Unitary.toUnits κ)) 1 = 0 := by
    intro w hw
    simp only [MatrixCoefficientAnalytic.matrixCoefficient]
    rw [integral_map_toUnitaryGroup (f := fun y => w (y * 1) * h y) (hcont w hw 1)]
    simp only [mul_one]
    exact horth w hw
  have h2 := MatrixCoefficientAnalytic.matrixCoefficient_eq_zero μ (fun l => -e l) hχ.dual.eq hU
    hUK hUD hφ h1 u hu g
  simp only [MatrixCoefficientAnalytic.matrixCoefficient] at h2
  rwa [integral_map_toUnitaryGroup (f := fun y => u (y * g) * h y) (hcont u hu g)] at h2

/-! ## The induction -/

theorem isStrictlyDominant_shift {e : ℕ → ℂ} {m : ℕ} (he : IsStrictlyDominant e m) :
    IsStrictlyDominant (fun l => e l - 1 / 2) (m - 1) := by
  intro l hl
  have := he l (by omega)
  simp only [Complex.sub_re]
  linarith

/-- **Submodules of the dual principal series.** Let `χ` be strictly dominant signed-power
characters on `GL_n(ℝ)`, `U` a nonzero `(𝔤, K)`-stable subspace of the `O(n)`-finite functions
of the principal series of `χ⁻¹`, and `h` an `O(n)`-finite function of the principal series of
`χ` with `∫_{O(n)} u h = 0` for all `u ∈ U`. Then the Jacquet integral of `h` vanishes. -/
theorem jacquet_eq_zero : ∀ (n : ℕ) {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}, IsSignedPower χ e →
    IsStrictlyDominant e (n - 1) →
    ∀ {U : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)},
    U ≤ kFiniteFunctions (principalSeries ℝ n (dualChar χ)) (unitaryCompact ℝ n) →
    (∀ k ∈ unitaryCompact ℝ n, ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k u ∈ U) →
    (∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ u ∈ U, rightDerivative (matrixModel ℝ n) X u ∈ U) →
    U ≠ ⊥ →
    ∀ {h : Langlands.GeneralLinear n ℝ → ℂ},
    h ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) →
    (∀ u ∈ U, ∫ k, u (k : Langlands.GeneralLinear n ℝ) * h k ∂haarK n = 0) →
    jacquet n h = 0
  | 0, χ, e, _, _, U, _, _, _, hU0, h, _, horth => by
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      have hsub : ∀ g : Langlands.GeneralLinear 0 ℝ, g = 1 := fun g => Subsingleton.elim _ _
      have hu1 : u 1 ≠ 0 := fun h1 => hu0 (funext fun g => by rw [hsub g]; exact h1)
      have hint := horth u huU
      have hconst : (fun k : unitaryCompact ℝ 0 => u (k : Langlands.GeneralLinear 0 ℝ) * h k) =
          fun _ => u 1 * h 1 := funext fun k => by rw [hsub k]
      rw [hconst, integral_const, probReal_univ, one_smul] at hint
      exact (mul_eq_zero.mp hint).resolve_left hu1
  | m + 1, χ, e, hχ, he, U, hU, hUK, hUD, hU0, h, hh, horth => by
      have he' : IsStrictlyDominant e m := by simpa using he
      have hF3 := integral_mul_eq_zero_of_orthogonal hχ hU hUK hUD hh.1.1.continuous horth
      have hlim : ∀ u ∈ U, ∫ k, u (iotaGL (k : Langlands.GeneralLinear m ℝ)) *
          jacquetStep h k ∂haarK m = 0 := fun u hu =>
        integral_mul_jacquetStep_eq_zero hχ he' (hU hu).1 hh.1 (hF3 u hu)
      have hUM : U.map restrictLevi ≤
          kFiniteFunctions (principalSeries ℝ m (dualChar (shiftChar χ))) (unitaryCompact ℝ m) := by
        rintro _ ⟨u, hu, rfl⟩
        exact restrictLevi_mem hχ (hU hu)
      have hUMK : ∀ k ∈ unitaryCompact ℝ m, ∀ u ∈ U.map restrictLevi,
          Whittaker.rightTranslation ℂ (Langlands.GeneralLinear m ℝ) k u ∈ U.map restrictLevi := by
        rintro k hk _ ⟨u, hu, rfl⟩
        rw [rightTranslation_restrictLevi]
        exact ⟨_, hUK _ (iotaGL_mem_unitaryCompact hk) u hu, rfl⟩
      have hUMD : ∀ (X : Matrix (Fin m) (Fin m) ℝ), ∀ u ∈ U.map restrictLevi,
          rightDerivative (matrixModel ℝ m) X u ∈ U.map restrictLevi := by
        rintro X _ ⟨u, hu, rfl⟩
        rw [rightDerivative_restrictLevi (hU hu).1.1]
        exact ⟨_, hUD _ u hu, rfl⟩
      exact jacquet_eq_zero m hχ.shift (isStrictlyDominant_shift he') hUM hUMK hUMD
        (map_restrictLevi_ne_bot hU hUK hU0) (jacquetStep_mem hχ he' hh)
        (by rintro _ ⟨u, hu, rfl⟩; exact hlim u hu)

end JacquetDual

end Langlands.Archimedean
