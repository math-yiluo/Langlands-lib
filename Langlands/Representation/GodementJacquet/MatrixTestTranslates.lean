import Langlands.HarmonicAnalysis.SchwartzBruhatProduct
import Langlands.Group.GL.Basic

/-!
# Two-sided translates of full-matrix test functions

For a Schwartz–Bruhat function `Φ` on `n × n` matrices, the translates
`X ↦ Φ (u X u')` by `u, u' ∈ GL_n` are Schwartz–Bruhat, coincide with `Φ` for
`(u, u')` near `(1, 1)`, and, over a compact parameter space, form a finite
Schwartz–Bruhat combination of finitely many translates.
-/

noncomputable section

open Filter Topology

namespace Langlands.GodementJacquet

open HarmonicAnalysis

universe uR uK

variable {R : Type uR} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  {n : ℕ}

omit [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] in
private theorem inv_val_mul_val_mul (u : Langlands.GeneralLinear n R)
    (M : Matrix (Fin n) (Fin n) R) : (u⁻¹ : Langlands.GeneralLinear n R).val * (u.val * M) = M := by
  rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

omit [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] in
private theorem val_mul_inv_val_mul (u : Langlands.GeneralLinear n R)
    (M : Matrix (Fin n) (Fin n) R) : u.val * ((u⁻¹ : Langlands.GeneralLinear n R).val * M) = M := by
  rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

omit [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] in
private theorem val_mul_val_inv (u : Langlands.GeneralLinear n R) :
    u.val * (u⁻¹ : Langlands.GeneralLinear n R).val = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- The two-sided translate `X ↦ Φ (u X u')` of a full-matrix test function. -/
def matrixTranslate (Φ : SchwartzBruhat (Matrix (Fin n) (Fin n) R))
    (u u' : Langlands.GeneralLinear n R) : SchwartzBruhat (Matrix (Fin n) (Fin n) R) :=
  SchwartzBruhat.compLeftInverse Φ (fun X => u.val * X * u'.val)
    (fun X => (u⁻¹ : Langlands.GeneralLinear n R).val * X * (u'⁻¹ : Langlands.GeneralLinear n R).val)
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
    (fun X => by
      simp only [Matrix.mul_assoc, val_mul_val_inv, Matrix.mul_one, inv_val_mul_val_mul])

@[simp] theorem matrixTranslate_apply (Φ : SchwartzBruhat (Matrix (Fin n) (Fin n) R))
    (u u' : Langlands.GeneralLinear n R) (X : Matrix (Fin n) (Fin n) R) :
    matrixTranslate Φ u u' X = Φ (u.val * X * u'.val) := rfl

omit [T2Space R] in
/-- On the support of `Φ`, two-sided translation near `(1, 1)` does not change `Φ`. -/
private theorem eventually_translate_eq_on_support
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin n) R)) :
    ∀ᶠ g in 𝓝 ((1, 1) : Langlands.GeneralLinear n R × Langlands.GeneralLinear n R),
      ∀ Y ∈ tsupport (Φ : Matrix (Fin n) (Fin n) R → ℂ), Φ (g.1.val * Y * g.2.val) = Φ Y := by
  apply Φ.hasCompactSupport.isCompact.eventually_forall_of_forall_eventually
  intro Y _
  have hact : Continuous fun w : (Langlands.GeneralLinear n R × Langlands.GeneralLinear n R) ×
      Matrix (Fin n) (Fin n) R => w.1.1.val * w.2 * w.1.2.val :=
    ((Units.continuous_val.comp (continuous_fst.comp continuous_fst)).matrix_mul
      continuous_snd).matrix_mul (Units.continuous_val.comp (continuous_snd.comp continuous_fst))
  have h1 : ∀ᶠ w in 𝓝 (((1, 1) : Langlands.GeneralLinear n R × Langlands.GeneralLinear n R), Y),
      Φ (w.1.1.val * w.2 * w.1.2.val) = Φ Y := by
    have ht := hact.tendsto (((1, 1) : Langlands.GeneralLinear n R × Langlands.GeneralLinear n R), Y)
    simp only [Units.val_one, Matrix.one_mul, Matrix.mul_one] at ht
    exact ht.eventually (Φ.locallyConstant.eventually_eq Y)
  have h2 : ∀ᶠ w in 𝓝 (((1, 1) : Langlands.GeneralLinear n R × Langlands.GeneralLinear n R), Y),
      Φ w.2 = Φ Y :=
    (continuous_snd.tendsto
      (((1, 1) : Langlands.GeneralLinear n R × Langlands.GeneralLinear n R), Y)).eventually
      (Φ.locallyConstant.eventually_eq Y)
  filter_upwards [h1, h2] with w hw1 hw2
  exact hw1.trans hw2.symm

omit [T2Space R] in
/-- **Two-sided stabilizer.** Near `(1, 1)`, two-sided translation fixes `Φ`. -/
theorem eventually_matrixTranslate_eq (Φ : SchwartzBruhat (Matrix (Fin n) (Fin n) R)) :
    ∀ᶠ g in 𝓝 ((1, 1) : Langlands.GeneralLinear n R × Langlands.GeneralLinear n R),
      ∀ Y, Φ (g.1.val * Y * g.2.val) = Φ Y := by
  have hinv : Tendsto (fun g : Langlands.GeneralLinear n R × Langlands.GeneralLinear n R =>
      (g.1⁻¹, g.2⁻¹)) (𝓝 (1, 1)) (𝓝 (1, 1)) := by
    have := ((continuous_inv.comp continuous_fst).prodMk
      (continuous_inv.comp continuous_snd)).tendsto
      ((1, 1) : Langlands.GeneralLinear n R × Langlands.GeneralLinear n R)
    simpa using this
  filter_upwards [eventually_translate_eq_on_support Φ,
    hinv.eventually (eventually_translate_eq_on_support Φ)] with g hg hg'
  intro Y
  by_cases hY : Y ∈ tsupport (Φ : Matrix (Fin n) (Fin n) R → ℂ)
  · exact hg Y hY
  · by_cases hZ : g.1.val * Y * g.2.val ∈ tsupport (Φ : Matrix (Fin n) (Fin n) R → ℂ)
    · have h := hg' _ hZ
      rw [← h]
      simp only [Matrix.mul_assoc, val_mul_val_inv, Matrix.mul_one, inv_val_mul_val_mul]
    · rw [image_eq_zero_of_notMem_tsupport hZ, image_eq_zero_of_notMem_tsupport hY]

omit [T2Space R] in
/-- The family of two-sided translates along a continuous map is locally constant. -/
theorem isLocallyConstant_matrixTranslate {K : Type uK} [TopologicalSpace K]
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin n) R))
    (a b : K → Langlands.GeneralLinear n R) (ha : Continuous a) (hb : Continuous b) :
    IsLocallyConstant fun k : K => fun X : Matrix (Fin n) (Fin n) R =>
      Φ ((a k).val * X * (b k).val) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro k
  have hc1 : Continuous fun k' : K => a k' * (a k)⁻¹ := ha.mul continuous_const
  have hc2 : Continuous fun k' : K => (b k)⁻¹ * b k' := continuous_const.mul hb
  have ht : Tendsto (fun k' : K => (a k' * (a k)⁻¹, (b k)⁻¹ * b k')) (𝓝 k) (𝓝 (1, 1)) := by
    have := (hc1.prodMk hc2).tendsto k
    simpa using this
  filter_upwards [ht.eventually (eventually_matrixTranslate_eq Φ)] with k' hk'
  funext X
  have h := hk' ((a k).val * X * (b k).val)
  rw [← h]
  simp only [Units.val_mul, Matrix.mul_assoc, inv_val_mul_val_mul, val_mul_inv_val_mul]

omit [T2Space R] in
/-- **Finite translate expansion.** Over a compact space of continuous
parameters, the translates `Φ (a k X b k)` are a finite Schwartz–Bruhat
combination of finitely many of them. -/
theorem exists_matrixTranslate_expansion {K : Type uK} [TopologicalSpace K] [CompactSpace K]
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin n) R))
    (a b : K → Langlands.GeneralLinear n R) (ha : Continuous a) (hb : Continuous b) :
    ∃ (L : ℕ) (χ : Fin L → SchwartzBruhat K) (r : Fin L → K),
      ∀ k X, Φ ((a k).val * X * (b k).val) =
        ∑ l, χ l k * Φ ((a (r l)).val * X * (b (r l)).val) := by
  obtain ⟨L, χ, r, hr⟩ := exists_finite_schwartz_expansion
    (fun k : K => fun X : Matrix (Fin n) (Fin n) R => Φ ((a k).val * X * (b k).val))
    (isLocallyConstant_matrixTranslate Φ a b ha hb)
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
  exact ⟨L, χ, r, fun k X => hr X k⟩

end Langlands.GodementJacquet
