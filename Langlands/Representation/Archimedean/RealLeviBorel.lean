import Langlands.Representation.Archimedean.RealLeviTwoBlock

/-!
# The `O(N)`-integral in coordinates of the opposite unipotent radical of the Borel subgroup

Tools for the proof of `RealLeviParabolicIntegrationStatement`.

For the identity position function `vcl N : Fin N → ℕ` (`p ↦ p`), the chart coordinates
`CoordC (vcl N)` are the entries `Y_{pq}`, `q < p`, of the lower unitriangular group `N̄_B`.
The theorem `integral_eq_borel` says: there is `C_N > 0` such that
`∫_{O(N)} F = C_N ∫ F(n̄(Y)) dY` for every smooth `F` on `GL_N(ℝ)` with
`F(diag(t) u g) = δ_B(t) F(g)`. It is proved by induction on `N` from the Library's
maximal-parabolic integration formula `integral_eq_chart`
(`∫_{O(m+1)} F = c_m ∫_v ∫_{O(m)} F(ι(k) J(v, 1)) dk dv`), the induction hypothesis applied to the
Levi slice `leviSlice F (J(v, 1))` and the identity `ι(n̄(Y')) J(v, 1) = n̄(Y)` where `Y` puts the
entries `Y'` and the last row `v` together.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviBorel

open GramFormula MaximalParabolicIntegration RealLeviChartGram RealLeviChartIntegrable
  RealLeviTwoBlock RealPrincipalSeriesDuality Langlands.GeneralLinear

attribute [local instance] measurableSpaceK

/-! ## The coordinates of `N̄_B` -/

/-- The identity position function `p ↦ p`; its chart is the lower unitriangular group. -/
def vcl (N : ℕ) : Fin N → ℕ := fun p => (p : ℕ)

theorem vcl_monotone (N : ℕ) : Monotone (vcl N) := fun _ _ h => h

instance : IsEmpty (CoordC (vcl 0)) := ⟨fun x => x.1.1.elim0⟩

variable (m : ℕ)

/-- The last row and the coordinates of `N̄_B` of `GL_m` as coordinates of `N̄_B` of
`GL_{m+1}`. -/
def toCoordB : Fin m ⊕ CoordC (vcl m) → CoordC (vcl (m + 1))
  | .inl j => ⟨(Fin.last m, Fin.castSucc j), j.isLt⟩
  | .inr x => ⟨(Fin.castSucc x.1.1, Fin.castSucc x.1.2), x.2⟩

theorem toCoordB_bijective : Function.Bijective (toCoordB m) := by
  constructor
  · rintro (j | ⟨⟨p, q⟩, hx⟩) (j' | ⟨⟨p', q'⟩, hy⟩) h <;>
      replace h := congrArg Subtype.val h <;>
      simp only [toCoordB, Prod.mk.injEq] at h
    · rw [Fin.castSucc_inj] at h
      rw [h.2]
    · exact absurd h.1 (Fin.castSucc_lt_last p').ne'
    · exact absurd h.1 (Fin.castSucc_lt_last p).ne
    · rw [Fin.castSucc_inj, Fin.castSucc_inj] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  · rintro ⟨⟨p, q⟩, h⟩
    induction p using Fin.lastCases with
    | last =>
      induction q using Fin.lastCases with
      | last => exact absurd h (lt_irrefl _)
      | cast j => exact ⟨.inl j, rfl⟩
    | cast i =>
      induction q using Fin.lastCases with
      | last =>
        exfalso
        have h' : m < (i : ℕ) := h
        exact absurd i.isLt (not_lt.mpr h'.le)
      | cast j => exact ⟨.inr ⟨(i, j), h⟩, rfl⟩

/-- `(v, Y') ↦ Y`: the last row `v` and the coordinates `Y'` put together. -/
def embedB : ((Fin m → ℝ) × (CoordC (vcl m) → ℝ)) ≃ᵐ (CoordC (vcl (m + 1)) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ CoordC (vcl m) => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (Equiv.ofBijective _ (toCoordB_bijective m)))

theorem measurePreserving_embedB : MeasurePreserving (embedB m) volume volume := by
  have h1 := measurePreserving_piCongrLeft (fun _ : CoordC (vcl (m + 1)) => (volume : Measure ℝ))
    (Equiv.ofBijective _ (toCoordB_bijective m))
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin m ⊕ CoordC (vcl m) => ℝ)
  exact h1.comp h2

theorem embedB_inl (v : Fin m → ℝ) (Y' : CoordC (vcl m) → ℝ) (j : Fin m) :
    embedB m (v, Y') (toCoordB m (.inl j)) = v j := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (Equiv.ofBijective _ (toCoordB_bijective m)) (β := fun _ => ℝ)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ CoordC (vcl m) => ℝ)).symm (v, Y'))
    (.inl j)
  exact h

theorem embedB_inr (v : Fin m → ℝ) (Y' : CoordC (vcl m) → ℝ) (x : CoordC (vcl m)) :
    embedB m (v, Y') (toCoordB m (.inr x)) = Y' x := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (Equiv.ofBijective _ (toCoordB_bijective m)) (β := fun _ => ℝ)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ CoordC (vcl m) => ℝ)).symm (v, Y'))
    (.inr x)
  exact h

/-! ## `ι(n̄(Y')) J(v, 1) = n̄(Y)` -/

theorem iota_mul_Jmat_castSucc (A : Matrix (Fin m) (Fin m) ℝ) (r : Fin (m + 1) → ℝ)
    (i : Fin m) (j : Fin m) : (iota A * Jmat r) i.castSucc j.castSucc = A i j := by
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Jmat, Matrix.one_apply]

theorem iota_mul_Jmat_castSucc_last (A : Matrix (Fin m) (Fin m) ℝ) (r : Fin (m + 1) → ℝ)
    (i : Fin m) : (iota A * Jmat r) i.castSucc (Fin.last m) = 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Jmat, Matrix.one_apply,
    (Fin.castSucc_lt_last _).ne]

theorem iota_mul_Jmat_last (A : Matrix (Fin m) (Fin m) ℝ) (r : Fin (m + 1) → ℝ)
    (j : Fin (m + 1)) : (iota A * Jmat r) (Fin.last m) j = r j := by
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Jmat]

theorem iota_lowerC_mul_Jmat (v : Fin m → ℝ) (Y' : CoordC (vcl m) → ℝ) :
    iota (lowerC (vcl m) Y') * Jmat (Fin.snoc v 1) = lowerC (vcl (m + 1)) (embedB m (v, Y')) := by
  ext p q
  induction p using Fin.lastCases with
  | last =>
    rw [iota_mul_Jmat_last]
    induction q using Fin.lastCases with
    | last =>
      have hn : ¬ vcl (m + 1) (Fin.last m) < vcl (m + 1) (Fin.last m) := lt_irrefl _
      rw [Fin.snoc_last, lowerC, of_apply, dite_eq_right hn]
      simp
    | cast j =>
      have hj : vcl (m + 1) (Fin.castSucc j) < vcl (m + 1) (Fin.last m) := j.isLt
      rw [Fin.snoc_castSucc, lowerC, of_apply, dite_eq_left hj]
      exact (embedB_inl m v Y' j).symm
  | cast i =>
    induction q using Fin.lastCases with
    | last =>
      have hn : ¬ vcl (m + 1) (Fin.last m) < vcl (m + 1) (Fin.castSucc i) := fun h =>
        absurd i.isLt (not_lt.mpr (show m < (i : ℕ) from h).le)
      rw [iota_mul_Jmat_castSucc_last, lowerC, of_apply, dite_eq_right hn,
        ite_eq_right_iff.mpr fun h => absurd h (Fin.castSucc_lt_last i).ne]
    | cast j =>
      rw [iota_mul_Jmat_castSucc]
      by_cases hij : vcl m j < vcl m i
      · have hij' : vcl (m + 1) (Fin.castSucc j) < vcl (m + 1) (Fin.castSucc i) := hij
        rw [lowerC, of_apply, dite_eq_left hij, lowerC, of_apply, dite_eq_left hij']
        exact (embedB_inr m v Y' ⟨(i, j), hij⟩).symm
      · have hij' : ¬ vcl (m + 1) (Fin.castSucc j) < vcl (m + 1) (Fin.castSucc i) := hij
        rw [lowerC, of_apply, dite_eq_right hij, lowerC, of_apply, dite_eq_right hij']
        simp only [Fin.castSucc_inj]

theorem iotaGL_lowerCGL_mul_chartGL (v : Fin m → ℝ) (Y' : CoordC (vcl m) → ℝ) :
    iotaGL (lowerCGL (vcl_monotone m) Y') * chartGL v =
      lowerCGL (vcl_monotone (m + 1)) (embedB m (v, Y')) := by
  ext : 1
  rw [Units.val_mul, iotaGL_val, lowerCGL_val, lowerCGL_val, chartGL, JGL_val]
  exact iota_lowerC_mul_Jmat m v Y'

/-! ## The integration formula -/

/-- **The `O(N)`-integral in coordinates of `N̄_B`.** There is `C_N > 0` with
`∫_{O(N)} F = C_N ∫ F(n̄(Y)) dY` for every smooth `F` with `F(diag(t) u g) = δ_B(t) F(g)`. -/
theorem integral_eq_borel : ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ F : Langlands.GeneralLinear N ℝ → ℂ,
    ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ F → IsModulusCovariant F →
      ∫ κ, F (κ : Langlands.GeneralLinear N ℝ) ∂haarK N =
        (C : ℂ) * ∫ Y : CoordC (vcl N) → ℝ, F (lowerCGL (vcl_monotone N) Y)
  | 0 => by
    refine ⟨1, one_pos, fun F _ _ => ?_⟩
    have h1 : ∀ κ : unitaryCompact ℝ 0, F (κ : Langlands.GeneralLinear 0 ℝ) = F 1 :=
      fun κ => congrArg F (Subsingleton.elim _ _)
    have h2 : ∀ Y : CoordC (vcl 0) → ℝ, F (lowerCGL (vcl_monotone 0) Y) = F 1 :=
      fun Y => congrArg F (Subsingleton.elim _ _)
    simp only [h1, h2, integral_const, probReal_univ, one_smul, Complex.ofReal_one, one_mul]
    rw [Measure.real, volume_univ_of_isEmpty, ENNReal.toReal_one, one_smul]
  | m + 1 => by
    obtain ⟨C, hC, hBF⟩ := integral_eq_borel m
    refine ⟨chartConstant m * C, mul_pos (chartConstant_pos m) hC, fun F hFs hF => ?_⟩
    rw [integral_eq_chart hFs hF]
    have hv : ∀ v : Fin m → ℝ, natural F (chartGL v) =
        (C : ℂ) * ∫ Y' : CoordC (vcl m) → ℝ,
          F (lowerCGL (vcl_monotone (m + 1)) (embedB m (v, Y'))) := by
      intro v
      have h1 : natural F (chartGL v) =
          ∫ k : unitaryCompact ℝ m, leviSlice F (chartGL v) (k : Langlands.GeneralLinear m ℝ)
            ∂haarK m := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        simp only [leviSlice, abs_det_unitary k, Complex.ofReal_one, inv_one, mul_one]
      rw [h1, hBF _ (contMDiff_leviSlice hFs _) (leviSlice_covariant hF _)]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun Y' => ?_)
      simp only [leviSlice, lowerCGL_val, det_lowerC (vcl_monotone m), abs_one, Complex.ofReal_one,
        inv_one, mul_one]
      rw [iotaGL_lowerCGL_mul_chartGL]
    have hG : Integrable fun Y : CoordC (vcl (m + 1)) → ℝ =>
        F (lowerCGL (vcl_monotone (m + 1)) Y) := by
      have h := integrable_comp_lowerCGL hFs hF (vcl_monotone (m + 1))
        (one_mem (unitaryCompact ℝ (m + 1)))
      simpa only [mul_one] using h
    have hG2 := (measurePreserving_embedB m).integrable_comp_of_integrable hG
    have h3 := (measurePreserving_embedB m).integral_comp'
      (fun Y => F (lowerCGL (vcl_monotone (m + 1)) Y))
    rw [Measure.volume_eq_prod] at h3 hG2
    rw [integral_congr_ae (ae_of_all _ hv), integral_const_mul,
      ← integral_prod (fun z => F (lowerCGL (vcl_monotone (m + 1)) (embedB m z))) hG2, h3,
      Complex.ofReal_mul, mul_assoc]

end RealLeviBorel

end Langlands.Archimedean
