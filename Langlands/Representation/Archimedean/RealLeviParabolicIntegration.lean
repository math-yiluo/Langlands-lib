import Langlands.Representation.Archimedean.RealLeviShear
import Langlands.Representation.Archimedean.RealLeviBlockDecomposition

/-!
# Proof of `RealLeviParabolicIntegrationStatement`

For block sizes `sz : Fin c → ℕ` with `N = ∑ i, sz i`, let `cls sz : Fin N → Fin c` be the
(monotone) block function, `K_M = ∏ᵢ O(sz_i)` with the product `μ_K` of the Haar probability
measures, and `diag(κ) = blockDiagGL sz κ`. For smooth `F` with `F(diag(t) u g) = δ_B(t) F(g)`:

1. `X ↦ F(n̄(X) diag(κ))` is integrable (`integrable_comp_lowerCGL`, from the Gram bound).
2. `∫_{K_M} ∫_X F(n̄(X) diag(κ)) = ∫_X ∫_{K_M} F(diag(κ) n̄(X))`: the map
   `(κ, X) ↦ (κ, Ad(diag κ) X)` preserves `μ_K ⊗ dX` (`measurePreserving_shiftAd`) and
   `diag(κ) n̄(X) = n̄(Ad(diag κ) X) diag(κ)` (`mul_lowerGL`).
3. `κ ↦ diag(κ)` is a continuous surjective homomorphism `K_M → Kc (cls sz)`, so it maps `μ_K`
   to the Haar probability measure `μc (cls sz)` (`map_bdK`), and `leviBorel` applied to the right
   translate `F(· n̄(X))` gives `∫_{K_M} F(diag(κ) n̄(X)) = C_M ∫_Z F(n̄_M(Z) n̄(X)) dZ`.
4. The shear `(Z, X) ↦ Y` with `n̄_B(Y) = n̄_M(Z) n̄(X)` preserves Lebesgue measure
   (`measurePreserving_shear`), so `∫_X ∫_Z F(n̄_M(Z) n̄(X)) = ∫_Y F(n̄_B(Y))`, and
   `∫_{O(N)} F = C_N ∫_Y F(n̄_B(Y))` (`integral_eq_borel`). Hence the statement holds with
   `C = C_N / C_M`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviParabolicIntegration

open GramFormula MaximalParabolicIntegration RealLeviChartGram RealLeviChartIntegrable
  RealLeviTwoBlock RealLeviBorel RealLeviBlockHaar RealLeviLeviBorel RealLeviShear
  RealPrincipalSeriesDuality RealLeviChart Langlands.GeneralLinear

attribute [local instance] measurableSpaceK RealLeviBlockHaar.secondCountableTopology_GL
  RealLeviBlockHaar.secondCountableTopology_O

local instance borelSpaceK_pi (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

/-! ## Right translates -/

section Translate

variable {N : ℕ} {F : Langlands.GeneralLinear N ℝ → ℂ}

theorem contMDiff_comp_mul_right (hF : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ F)
    (y : Langlands.GeneralLinear N ℝ) :
    ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ fun g => F (g * y) := by
  have h := contMDiff_mul_comp hF (MonoidHom.id _) (Φ := id) contDiff_id (fun _ => rfl) y
    (c := fun _ => (1 : ℂ)) contDiffOn_const
  simpa only [MonoidHom.id_apply, mul_one] using h

theorem isModulusCovariant_comp_mul_right (hF : IsModulusCovariant F)
    (y : Langlands.GeneralLinear N ℝ) : IsModulusCovariant fun g => F (g * y) := by
  intro a u g
  have h := hF a u (g * y)
  rwa [← mul_assoc] at h

end Translate

/-! ## The block diagonal decomposition of `Kc (cls sz)` -/

section Blocks

variable {c : ℕ} {sz : Fin c → ℕ}

theorem cls_monotone : Monotone (cls sz) := fun _ _ h => cls_mono sz h

/-- Every block orthogonal element is `diag(κ_0, …, κ_{c-1})` with `κ_i ∈ O(sz_i)`. -/
theorem exists_blockDiagGL_eq {g : Langlands.GeneralLinear (∑ i, sz i) ℝ}
    (hg : g ∈ blockOrth sz) :
    ∃ κ : ∀ i, unitaryCompact ℝ (sz i),
      blockDiagGL sz (fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ)) = g :=
  ⟨RealLeviTorus.orthBlock hg, RealLeviTorus.blockDiagGL_orthBlock hg⟩

/-- `diag(κ_0, …, κ_{c-1})` for `κ ∈ K_M = ∏_i O(sz_i)`. -/
abbrev bd (κ : ∀ i, unitaryCompact ℝ (sz i)) : Langlands.GeneralLinear (∑ i, sz i) ℝ :=
  blockDiagGL sz fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ)

theorem continuous_bd_val :
    Continuous fun κ : (∀ i, unitaryCompact ℝ (sz i)) =>
      ((bd κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) :=
  (Continuous.matrix_blockDiagonal' (continuous_pi fun i =>
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply i)))).matrix_reindex
      _ _

theorem continuous_bd : Continuous (bd (sz := sz)) := by
  refine Units.continuous_iff.mpr ⟨continuous_bd_val, ?_⟩
  have h : ∀ κ : (∀ i, unitaryCompact ℝ (sz i)),
      (((bd κ)⁻¹ : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
          Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) =
        ((bd κ⁻¹ : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
          Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) := by
    intro κ
    rw [bd, bd, ← map_inv]
    rfl
  exact (continuous_bd_val.comp (continuous_inv (G := ∀ i, unitaryCompact ℝ (sz i)))).congr
    fun κ => (h κ).symm

theorem bd_mem_Kc (κ : ∀ i, unitaryCompact ℝ (sz i)) : bd κ ∈ Kc (cls sz) :=
  ⟨blockDiagGL_mem_unitaryCompact κ, (blockDiagGL_mem_blockOrth κ).2⟩

/-- `κ ↦ diag(κ)` as a homomorphism `K_M → Kc (cls sz)`. -/
def bdK : (∀ i, unitaryCompact ℝ (sz i)) →* Kc (cls sz) where
  toFun κ := ⟨bd κ, bd_mem_Kc κ⟩
  map_one' := Subtype.ext (map_one (blockDiagGL sz))
  map_mul' κ ρ := Subtype.ext (by
    change bd (κ * ρ) = bd κ * bd ρ
    rw [bd, bd, bd, ← map_mul]
    rfl)

theorem bdK_val (κ : ∀ i, unitaryCompact ℝ (sz i)) :
    ((bdK κ : Kc (cls sz)) : Langlands.GeneralLinear (∑ i, sz i) ℝ) = bd κ :=
  rfl

theorem continuous_bdK : Continuous (bdK (sz := sz)) :=
  continuous_bd.subtype_mk _

theorem surjective_bdK : Function.Surjective (bdK (sz := sz)) := by
  rintro ⟨k, hk⟩
  obtain ⟨κ, hκ⟩ := exists_blockDiagGL_eq (mem_blockOrth_of_mem_unitaryCompact hk.1 hk.2)
  exact ⟨κ, Subtype.ext hκ⟩

/-- `μc (cls sz)` is the image of `μ_K = ∏_i haarK (sz i)` under `κ ↦ diag(κ)`. -/
theorem map_bdK :
    Measure.map (bdK (sz := sz)) (Measure.pi fun i => haarK (sz i)) = μc (cls sz) := by
  have : (Measure.map (bdK (sz := sz)) (Measure.pi fun i => haarK (sz i))).IsHaarMeasure :=
    Measure.isHaarMeasure_map_of_isFiniteMeasure _ bdK continuous_bdK surjective_bdK
  exact eq_μc (cls sz) _

/-- `∫_{K_M} f(diag(κ) y) dκ = ∫_{Kc (cls sz)} f(k y) dk`. -/
theorem integral_pi_mul_eq {f : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ} (hf : Continuous f)
    (y : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
    ∫ κ, f (bd κ * y) ∂Measure.pi (fun i => haarK (sz i)) =
      ∫ k, f ((k : Langlands.GeneralLinear (∑ i, sz i) ℝ) * y) ∂μc (cls sz) := by
  rw [← map_bdK, integral_map continuous_bdK.aemeasurable
    (f := fun k : Kc (cls sz) => f ((k : Langlands.GeneralLinear (∑ i, sz i) ℝ) * y))
    (hf.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable]
  rfl

end Blocks

/-! ## Moving `diag(κ)` to the left -/

section Shift

variable {c : ℕ} {sz : Fin c → ℕ}

theorem continuous_lower_sz : Continuous (lower sz) :=
  continuous_lowerC

theorem lowerGL_eq (X : Coord sz → ℝ) : lowerGL sz X = lowerCGL cls_monotone X :=
  Units.ext (by rw [lowerGL_val, lowerCGL_val]; rfl)

/-- `Ad(diag κ)` on the coordinates, as a function of `(κ, X)`. -/
def adBd (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Coord sz → ℝ) : Coord sz → ℝ :=
  adCoord ((bd κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
    Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) X

/-- `(κ, X) ↦ (κ, Ad(diag κ) X)`. -/
def shiftAd (p : (∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ)) :
    (∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ) :=
  (id p.1, adBd p.1 p.2)

theorem continuous_adBd : Continuous (Function.uncurry (adBd (sz := sz))) := by
  refine continuous_pi fun pq => ?_
  exact ((((continuous_bd_val.comp continuous_fst).matrix_mul
    (continuous_lower_sz.comp continuous_snd)).matrix_mul
      (continuous_bd_val.comp continuous_fst).matrix_transpose).matrix_elem _ _)

theorem map_adBd (κ : ∀ i, unitaryCompact ℝ (sz i)) :
    Measure.map (adBd κ) (volume : Measure (Coord sz → ℝ)) = volume :=
  (measurePreserving_adCoord (blockDiagGL_mem_blockOrth κ)).map_eq

/-- `(κ, X) ↦ (κ, Ad(diag κ) X)` preserves `μ_K ⊗ dX`. -/
theorem measurePreserving_shiftAd :
    MeasurePreserving (shiftAd (sz := sz)) ((Measure.pi fun i => haarK (sz i)).prod volume)
      ((Measure.pi fun i => haarK (sz i)).prod volume) := by
  have hm : Measurable (Function.uncurry (adBd (sz := sz))) := continuous_adBd.measurable
  have ha : ∀ᵐ κ ∂(Measure.pi fun i => haarK (sz i)),
      Measure.map (adBd κ) (volume : Measure (Coord sz → ℝ)) = volume :=
    ae_of_all _ map_adBd
  exact (MeasurePreserving.id (Measure.pi fun i => haarK (sz i))).skew_product hm ha

end Shift

/-! ## The iterated integral -/

section Main

variable {c : ℕ} {sz : Fin c → ℕ}

/-- **The iterated integral in Borel coordinates.** If `C_M` is the constant of `leviBorel` for
`cls sz`, then `∫_{K_M} ∫_X F(n̄(X) diag(κ)) = C_M ∫_Y F(n̄_B(Y))`. -/
theorem integral_integral_eq {CM : ℝ}
    (hBM : ∀ F : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ,
      ContMDiff (matrixModel ℝ (∑ i, sz i)) 𝓘(ℝ, ℂ) ∞ F → IsModulusCovariant F →
        ∫ k, F (k : Langlands.GeneralLinear (∑ i, sz i) ℝ) ∂μc (cls sz) =
          (CM : ℂ) * ∫ Z : CoordM (cls sz) → ℝ, F (lowerMGL (cls sz) Z))
    {F : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hFs : ContMDiff (matrixModel ℝ (∑ i, sz i)) 𝓘(ℝ, ℂ) ∞ F) (hF : IsModulusCovariant F) :
    ∫ κ : (∀ i, unitaryCompact ℝ (sz i)),
        (∫ X : Coord sz → ℝ, F (lowerGL sz X * bd κ)) ∂Measure.pi (fun i => haarK (sz i)) =
      (CM : ℂ) * ∫ Y : CoordC (vcl (∑ i, sz i)) → ℝ, F (lowerCGL (vcl_monotone _) Y) := by
  have hcl : Monotone (cls sz) := cls_monotone
  set μK : Measure (∀ i, unitaryCompact ℝ (sz i)) := Measure.pi fun i => haarK (sz i) with hμK
  let g : (∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ) → ℂ :=
    fun p => F (lowerGL sz p.2 * bd p.1)
  have hgc : Continuous g := by
    refine continuous_comp_of_val hFs ?_
    simp only [Units.val_mul, lowerGL_val]
    exact (continuous_lower_sz.comp continuous_snd).matrix_mul (continuous_bd_val.comp continuous_fst)
  have hgi : Integrable g (μK.prod volume) := by
    obtain ⟨B, hB⟩ := exists_bound hFs
    have hI : Integrable (fun X : Coord sz → ℝ =>
        ∏ l : Fin (∑ i, sz i), gram (l : ℕ) (lower sz X) ^ (-1 : ℝ)) :=
      integrable_prod_gram_inv hcl
    refine ((hI.const_mul B).comp_snd μK).mono' hgc.aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    have h := norm_le_gram_inv hF hB (lowerGL sz p.2)
      (by rw [lowerGL_val]; exact gram_zero_lowerC hcl p.2) (blockDiagGL_mem_unitaryCompact p.1)
    rw [lowerGL_val] at h
    exact h
  have hΨ := measurePreserving_shiftAd (sz := sz)
  have hshear := measurePreserving_shear hcl
  have hfc : Continuous fun Y : CoordC (vcl (∑ i, sz i)) → ℝ =>
      F (lowerCGL (vcl_monotone _) Y) := by
    refine continuous_comp_of_val hFs ?_
    simp only [lowerCGL_val]
    exact continuous_lowerC
  have hBint : Integrable fun Y : CoordC (vcl (∑ i, sz i)) → ℝ =>
      F (lowerCGL (vcl_monotone _) Y) := by
    simpa only [mul_one] using
      integrable_comp_lowerCGL hFs hF (vcl_monotone (∑ i, sz i))
        (one_mem (unitaryCompact ℝ (∑ i, sz i)))
  let H : (CoordM (cls sz) → ℝ) × (Coord sz → ℝ) → ℂ :=
    fun q => F (lowerMGL (cls sz) q.1 * lowerGL sz q.2)
  have hHeq : ∀ q, H q = F (lowerCGL (vcl_monotone _) (shear hcl q)) := by
    rintro ⟨Z, X⟩
    simp only [H]
    rw [lowerCGL_shear, lowerGL_eq]
  have hH : Integrable H (volume.prod volume) := by
    refine (hshear.integrable_comp_of_integrable hBint).congr (ae_of_all _ fun q => ?_)
    rw [Function.comp_apply, hHeq]
  calc ∫ κ, (∫ X : Coord sz → ℝ, F (lowerGL sz X * bd κ)) ∂μK
      = ∫ p, g p ∂(μK.prod volume) := (integral_prod g hgi).symm
    _ = ∫ p, g (shiftAd p) ∂(μK.prod volume) := by
        rw [← integral_map hΨ.measurable.aemeasurable hgc.aestronglyMeasurable, hΨ.map_eq]
    _ = ∫ X : Coord sz → ℝ, ∫ κ, g (shiftAd (κ, X)) ∂μK :=
        integral_prod_symm _ (hΨ.integrable_comp_of_integrable hgi)
    _ = ∫ X : Coord sz → ℝ, (CM : ℂ) * ∫ Z : CoordM (cls sz) → ℝ,
          F (lowerMGL (cls sz) Z * lowerGL sz X) := by
        refine integral_congr_ae (ae_of_all _ fun X => ?_)
        have h1 : ∀ κ : (∀ i, unitaryCompact ℝ (sz i)),
            g (shiftAd (κ, X)) = F (bd κ * lowerGL sz X) := by
          intro κ
          simp only [g, shiftAd, adBd, id]
          rw [mul_lowerGL (blockDiagGL_mem_blockOrth κ) X]
        simp only [h1]
        rw [integral_pi_mul_eq hFs.continuous (lowerGL sz X)]
        exact hBM _ (contMDiff_comp_mul_right hFs _) (isModulusCovariant_comp_mul_right hF _)
    _ = (CM : ℂ) * ∫ X : Coord sz → ℝ, ∫ Z : CoordM (cls sz) → ℝ,
          F (lowerMGL (cls sz) Z * lowerGL sz X) := integral_const_mul _ _
    _ = (CM : ℂ) * ∫ q, H q ∂(volume.prod volume) :=
        congrArg (fun t => (CM : ℂ) * t) (integral_prod_symm H hH).symm
    _ = (CM : ℂ) * ∫ Y : CoordC (vcl (∑ i, sz i)) → ℝ, F (lowerCGL (vcl_monotone _) Y) := by
        congr 1
        rw [← hshear.map_eq, integral_map hshear.measurable.aemeasurable hfc.aestronglyMeasurable]
        exact integral_congr_ae (ae_of_all _ hHeq)

end Main

end RealLeviParabolicIntegration

open RealPrincipalSeriesDuality RealLeviChart RealLeviChartIntegrable RealLeviTwoBlock
  RealLeviBorel RealLeviLeviBorel RealLeviParabolicIntegration in
attribute [local instance] measurableSpaceK in
/-- **Proof of `RealLeviParabolicIntegrationStatement`**, with `C = C_N / C_M` (`C_N` from
`integral_eq_borel`, `C_M` from `leviBorel` for the block function `cls sz`). -/
theorem realLeviParabolicIntegration : RealLeviParabolicIntegrationStatement := by
  intro c sz
  have hcl : Monotone (cls sz) := cls_monotone
  obtain ⟨CN, hCN, hBN⟩ := integral_eq_borel (∑ i, sz i)
  obtain ⟨-, CM, hCM, hBM⟩ := leviBorel (∑ i, sz i) (cls sz) hcl
  refine ⟨CN / CM, div_pos hCN hCM, fun F hFs hF => ⟨fun κ => ?_, ?_⟩⟩
  · refine (integrable_comp_lowerCGL hFs hF hcl (blockDiagGL_mem_unitaryCompact κ)).congr
      (ae_of_all _ fun X => ?_)
    simp only
    rw [lowerGL_eq]
  · have hCM0 : (CM : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hCM.ne'
    rw [hBN F hFs hF, integral_integral_eq hBM hFs hF, Complex.ofReal_div, ← mul_assoc,
      div_mul_cancel₀ _ hCM0]

end Langlands.Archimedean
