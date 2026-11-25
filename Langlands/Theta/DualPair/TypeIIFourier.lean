import Langlands.Theta.DualPair.TypeII
import Langlands.Theta.Heisenberg.SchrodingerFourier
import Langlands.Theta.Metaplectic.SiegelParabolic

/-!
# The type II splitting through the Fourier transform

GKT Proposition 12.21 (the splitting `s_ψ(g, h) = (m(g ⊗ h), 1)` of a type II pair through the
Siegel parabolic `P(𝕏)`, in the model `C_c^∞(𝕏^*)`) and §18.5.2 (p. 549: the passage to the model
`C_c^∞(𝕏)` "by the Fourier transform"), with Theorem 1.25 (p. 34) and Lemma 2.16 (p. 58).

`typeIISplitting` of `Langlands.Theta.DualPair.TypeII` is built in the model `S(X)` of the polarization `X × Y`
(`X = M_{n×m}(F)`, `Y = M_{m×n}(F)`, `β(x, y) = tr(x y)`), with the Siegel Levi of the Lagrangian
`0 × Y`; the book's `s_ψ` lives in the model `S(Y)` with the Siegel parabolic of `X × 0`. Here:

* `siegelLeviGroup.swap`: a Levi pair `(a, a')` of `β` is a Levi pair `(a', a)` of `-β.flip`;
  `det_siegelLevi_snd`: `det a' = (det a)⁻¹` for a perfect pairing;
* `schrodingerFourier_siegelLeviWeil`: **the Fourier transform `F_{Y,X}` carries the Levi operator
  of one model to that of the other**:
  `F (|det a|^{-1/2} φ(a⁻¹ ·)) = |det a'|^{-1/2} (F φ)(a'⁻¹ ·)`;
* `schrodingerFourier_typeIIWeil`: **`typeIISplitting` is the book's `s_ψ` through the Fourier
  transform**: `F ∘ typeIIWeil(g, h) = r'(m(g ⊗ h)) ∘ F`, where `r'` is the standard Weil operator
  of the polarization `Y × X` (functions on `Y = 𝕏^*`) at the image of `(g, h)` in its Siegel Levi
  (`standardOperator_siegelLevi`), i.e. the operator of the book's splitting
  `(g, h) ↦ (m(g ⊗ h), r(m(g ⊗ h)))`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal

namespace Langlands.Theta

open HeisenbergGroup Langlands.HarmonicAnalysis
open Langlands.LinearMap.BilinForm (isometryGroup)

universe u v w

section Levi

variable {R : Type u} [CommRing R] {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y] {β : X →ₗ[R] Y →ₗ[R] R}

variable (β) in
/-- A Levi pair `(a, a')` of `β` is the Levi pair `(a', a)` of `-β.flip` (the Siegel Levi of the
other Lagrangian). -/
def siegelLeviGroup.swap : siegelLeviGroup β →* siegelLeviGroup (-β.flip) where
  toFun m := ⟨(m.1.2, m.1.1), fun y x => by
    change -β (m.1.1 x) (m.1.2 y) = -β x y
    rw [m.2]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem siegelLeviGroup.swap_apply (m : siegelLeviGroup β) :
    (siegelLeviGroup.swap β m : (Y ≃ₗ[R] Y) × (X ≃ₗ[R] X)) = (m.1.2, m.1.1) := rfl

/-- `-p` is perfect when `p` is. -/
instance isPerfPair_neg {K M N : Type*} [Field K] [AddCommGroup M] [AddCommGroup N] [Module K M]
    [Module K N] [FiniteDimensional K M] (p : M →ₗ[K] N →ₗ[K] K) [p.IsPerfPair] :
    (-p).IsPerfPair :=
  LinearMap.IsPerfPair.of_injective
    (fun x x' h => (LinearMap.IsPerfPair.bijective_left p).1 (neg_injective h))
    (fun y y' h => (LinearMap.IsPerfPair.bijective_right p).1 (LinearMap.ext fun x => by
      have := LinearMap.congr_fun h x
      simpa using this))

end Levi

section DetLevi

variable {F : Type u} [Field F] {X : Type v} {Y : Type w} [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y] {β : X →ₗ[F] Y →ₗ[F] F}

/-- **`det a' = (det a)⁻¹`** for a Levi pair `(a, a')` of a perfect pairing: `a'` is the inverse of
the transpose of `a` through `X ≃ Y^*`. -/
theorem det_siegelLevi_snd [β.IsPerfPair] [FiniteDimensional F X] [FiniteDimensional F Y]
    (m : siegelLeviGroup β) :
    LinearEquiv.det m.1.2 = (LinearEquiv.det m.1.1)⁻¹ := by
  set e := β.toPerfPair
  have h : (m.1.1 : X →ₗ[F] X) = (e.symm : Module.Dual F Y →ₗ[F] X) ∘ₗ
      (m.1.2.symm : Y →ₗ[F] Y).dualMap ∘ₗ (e : X →ₗ[F] Module.Dual F Y) := by
    refine LinearMap.ext fun x => e.injective ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply]
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.dualMap_apply, LinearMap.toPerfPair_apply, LinearMap.toPerfPair_apply]
    have := m.2 x (m.1.2.symm y)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this
  have hdet : LinearMap.det (m.1.1 : X →ₗ[F] X) = LinearMap.det (m.1.2.symm : Y →ₗ[F] Y) := by
    rw [h, ← LinearMap.det_dualMap (m.1.2.symm : Y →ₗ[F] Y)]
    have := LinearMap.det_conj ((m.1.2.symm : Y →ₗ[F] Y).dualMap) e.symm
    rw [LinearEquiv.symm_symm] at this
    exact this
  have h2 : LinearMap.det (m.1.2.symm : Y →ₗ[F] Y) = ((LinearEquiv.det m.1.2 : Fˣ) : F)⁻¹ := by
    rw [← LinearEquiv.coe_det, LinearEquiv.det_symm, map_inv, Units.val_inv_eq_inv_val]
  refine Units.ext ?_
  rw [Units.val_inv_eq_inv_val, LinearEquiv.coe_det m.1.1, hdet, h2, inv_inv]

end DetLevi

section Fourier

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X]
  {Y : Type w} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y] [IsTopologicalAddGroup Y]
  {β : X →ₗ[F] Y →ₗ[F] F} {ψ : AddChar F ℂ}
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] [β.IsPerfPair]
  (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (μ : Measure X) [μ.IsAddHaarMeasure]

omit [Invertible (2 : F)] [MeasurableSpace Y] [BorelSpace Y] in
/-- **The Fourier transform carries the Levi operators of one Schrödinger model to the other's**:
`F (|det a|^{-1/2} φ(a⁻¹ ·)) = |det a'|^{-1/2} (F φ)(a'⁻¹ ·)` for a Levi pair `(a, a')`
(GKT p. 549, with `det a' = (det a)⁻¹`). -/
theorem schrodingerFourier_siegelLeviWeil (m : siegelLeviGroup β) (φ : SchwartzBruhat X) :
    schrodingerFourier β hψ hψ1 μ (siegelLeviWeil β m φ) =
      siegelLeviWeil (-β.flip) (siegelLeviGroup.swap β m) (schrodingerFourier β hψ hψ1 μ φ) := by
  refine Subtype.ext (funext fun y => ?_)
  set a := m.1.1
  set a' := m.1.2
  set D : ℝ≥0 := distribHaarChar F (LinearEquiv.det a)
  have hD : D ≠ 0 := (distribHaarChar_pos).ne'
  have hc := integral_comp_linearEquiv μ a
    (fun x => ψ (β x y) * (((D ^ (-(1 : ℝ) / 2) : ℝ≥0) : ℂ) * (φ : X → ℂ) (a.symm x)))
  simp only [LinearEquiv.symm_apply_apply] at hc
  have hβa : ∀ x, β (a x) y = β x (a'.symm y) := fun x => by
    have := m.2 x (a'.symm y)
    rwa [LinearEquiv.apply_symm_apply] at this
  simp only [hβa] at hc
  rw [schrodingerFourier_apply, siegelLeviWeil_apply, schrodingerFourier_apply]
  change ∫ x, ψ (β x y) * (((D ^ (-(1 : ℝ) / 2) : ℝ≥0) : ℂ) * (φ : X → ℂ) (a.symm x)) ∂μ =
    ((distribHaarChar F (LinearEquiv.det a') ^ (-(1 : ℝ) / 2) : ℝ≥0) : ℂ) *
      ∫ x, ψ (β x (a'.symm y)) * (φ : X → ℂ) x ∂μ
  have h1 : ∫ x, ψ (β x y) * (((D ^ (-(1 : ℝ) / 2) : ℝ≥0) : ℂ) * (φ : X → ℂ) (a.symm x)) ∂μ =
      (D : ℂ) * ∫ x, ψ (β x (a'.symm y)) * (((D ^ (-(1 : ℝ) / 2) : ℝ≥0) : ℂ) * (φ : X → ℂ) x)
        ∂μ := by
    rw [hc, NNReal.smul_def, Complex.real_smul, ← mul_assoc, NNReal.coe_inv, Complex.ofReal_inv,
      mul_inv_cancel₀ (by exact_mod_cast hD), one_mul]
  have hdet : distribHaarChar F (LinearEquiv.det a') = D⁻¹ := by
    rw [det_siegelLevi_snd m, map_inv]
  have hN : D * D ^ (-(1 : ℝ) / 2) = D⁻¹ ^ (-(1 : ℝ) / 2) := by
    have e1 : D * D ^ (-(1 : ℝ) / 2) = D ^ ((1 : ℝ) / 2) := by
      have h := NNReal.rpow_add hD (1 : ℝ) (-(1 : ℝ) / 2)
      rw [NNReal.rpow_one] at h
      rw [← h]
      norm_num
    rw [e1, NNReal.inv_rpow, ← NNReal.rpow_neg]
    norm_num
  have hscal : (D : ℂ) * ((D ^ (-(1 : ℝ) / 2) : ℝ≥0) : ℂ) =
      ((D⁻¹ ^ (-(1 : ℝ) / 2) : ℝ≥0) : ℂ) := by
    rw [← hN]; push_cast; ring
  rw [h1, hdet, ← hscal]
  simp_rw [mul_left_comm _ (((D ^ (-(1 : ℝ) / 2) : ℝ≥0) : ℂ))]
  rw [integral_const_mul]
  ring

end Fourier

section TypeII

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The trace pairing `(x, y) ↦ tr(x y)` of `M_{n×m}(F)` and `M_{m×n}(F)` is perfect. -/
instance isPerfPair_typeIIPairing (m n : ℕ) : (typeIIPairing F m n).IsPerfPair :=
  LinearMap.IsPerfPair.of_injective
    (fun _ _ h => Matrix.ext_iff_trace_mul_right.2 fun y => LinearMap.congr_fun h y)
    (fun _ _ h => Matrix.ext_iff_trace_mul_left.2 fun x => LinearMap.congr_fun h x)

attribute [local instance] isModuleTopology_matrix

variable [Invertible (2 : F)] {ψ : AddChar F ℂ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m n : ℕ}
  [MeasurableSpace (Matrix (Fin n) (Fin m) F)] [BorelSpace (Matrix (Fin n) (Fin m) F)]
  [MeasurableSpace (Matrix (Fin m) (Fin n) F)] [BorelSpace (Matrix (Fin m) (Fin n) F)]
  (μ : Measure (Matrix (Fin n) (Fin m) F)) [μ.IsAddHaarMeasure]

/-- **`typeIISplitting` is the book's `s_ψ` through the Fourier transform** (GKT Proposition 12.21,
§18.5.2, p. 549): the Fourier transform `F_{Y,X}` from the model `S(M_{n×m}(F))` of
`typeIISplitting` to the model `S(M_{m×n}(F))` of the book carries `typeIIWeil (g, h)` to the
standard Weil operator `r(m(g ⊗ h))` of the book's polarization (Lagrangian `𝕏 = M_{n×m}(F) × 0`,
functions on `𝕏^* = M_{m×n}(F)`), the operator of `s_ψ(g, h) = (m(g ⊗ h), r(m(g ⊗ h)))`. -/
theorem schrodingerFourier_typeIIWeil (g : GeneralLinear m F) (h : GeneralLinear n F)
    (φ : SchwartzBruhat (Matrix (Fin n) (Fin m) F)) :
    schrodingerFourier (typeIIPairing F m n) hψ hψ1 μ (typeIIWeil F m n (g, h) φ) =
      standardOperator hψ hψ1 (siegelLeviGroup.toIsometry (-(typeIIPairing F m n).flip)
          (siegelLeviGroup.swap _ (typeIILevi F m n (g, h))))
        (schrodingerFourier (typeIIPairing F m n) hψ hψ1 μ φ) := by
  have h1 : typeIIWeil F m n (g, h) φ =
      siegelLeviWeil (typeIIPairing F m n) (typeIILevi F m n (g, h)) φ := by
    rw [← weil_typeIISplitting hψ m n]
    rfl
  rw [h1, schrodingerFourier_siegelLeviWeil, standardOperator_siegelLevi]

end TypeII

end Langlands.Theta
