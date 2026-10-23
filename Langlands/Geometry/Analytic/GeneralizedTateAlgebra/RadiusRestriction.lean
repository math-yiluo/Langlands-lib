import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Embedding

/-! # Restriction of weighted series to smaller positive polyradii -/

noncomputable section

universe u v w

namespace Langlands.Analytic

namespace PositivePolyradius

/-- Decreasing all radii decreases every finite monomial weight. -/
theorem weight_mono {σ : Type u} (r s : PositivePolyradius σ)
    (hsr : ∀ i, s i ≤ r i) (d : σ →₀ ℕ) :
    s.weight d ≤ r.weight d := by
  apply Finset.prod_le_prod₀
  · intro i _
    exact pow_nonneg (s.positive i).le _
  · intro i _
    exact pow_le_pow_left₀ (s.positive i).le (hsr i) _

/-- Coordinatewise inequalities are preserved by finite concatenation. -/
theorem append_mono {n m : ℕ}
    (r r' : PositivePolyradius (Fin n)) (s s' : PositivePolyradius (Fin m))
    (hr : ∀ i, r' i ≤ r i) (hs : ∀ j, s' j ≤ s j) :
    ∀ k, r'.append s' k ≤ r.append s k := by
  intro k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa using hr i
  · simpa using hs j

end PositivePolyradius

namespace GeneralizedTateAlgebra

section GeneralCoefficients

variable {σ : Type u} (r s : PositivePolyradius σ)
  (hsr : ∀ i, s i ≤ r i)
  (K : Type v) [NormedCommRing K] [IsUltrametricDist K]

include hsr in
/-- The same formal series is restricted at every smaller positive polyradius. -/
theorem isRestricted_of_radius_le (f : GeneralizedTateAlgebra r K) :
    MvPowerSeries.IsRestricted s (series r K f) := by
  exact squeeze_zero
    (fun d => mul_nonneg (norm_nonneg _) (s.weight_pos d).le)
    (fun d => mul_le_mul_of_nonneg_left (r.weight_mono s hsr d) (norm_nonneg _))
    f.property

/-- Restrict by retaining all formal coefficients and decreasing the radii. -/
def restrictRadius : GeneralizedTateAlgebra r K →ₐ[K] GeneralizedTateAlgebra s K :=
  Subalgebra.inclusion (fun f hf => isRestricted_of_radius_le r s hsr K ⟨f, hf⟩)

@[simp] theorem series_restrictRadius (f : GeneralizedTateAlgebra r K) :
    series s K (restrictRadius r s hsr K f) = series r K f :=
  Subalgebra.coe_inclusion _ f

@[simp] theorem coeff_restrictRadius (f : GeneralizedTateAlgebra r K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (series s K (restrictRadius r s hsr K f)) =
      MvPowerSeries.coeff d (series r K f) :=
  congrArg (MvPowerSeries.coeff d) (series_restrictRadius r s hsr K f)

theorem restrictRadius_injective : Function.Injective (restrictRadius r s hsr K) := by
  intro f g h
  apply Subtype.ext
  change series r K f = series r K g
  simpa only [series_restrictRadius] using congrArg (series s K) h

/-- The restriction is contractive for the actual weighted Gauss norms. -/
theorem norm_restrictRadius_le (f : GeneralizedTateAlgebra r K) :
    ‖restrictRadius r s hsr K f‖ ≤ ‖f‖ := by
  apply (norm_le_iff s K _ (norm_nonneg f)).mpr
  intro d
  rw [coeff_restrictRadius]
  exact (mul_le_mul_of_nonneg_left (r.weight_mono s hsr d) (norm_nonneg _)).trans
    (weighted_norm_coeff_le r K f d)

@[simp] theorem restrictRadius_monomial (d : σ →₀ ℕ) (a : K) :
    restrictRadius r s hsr K (monomial r K d a) = monomial s K d a := by
  apply Subtype.ext
  exact series_restrictRadius r s hsr K (monomial r K d a)

@[simp] theorem restrictRadius_X (i : σ) :
    restrictRadius r s hsr K (X r K i) = X s K i := by
  apply Subtype.ext
  exact series_restrictRadius r s hsr K (X r K i)

@[simp] theorem restrictRadius_self (f : GeneralizedTateAlgebra r K) :
    restrictRadius r r (fun _ => le_rfl) K f = f := by
  apply Subtype.ext
  exact series_restrictRadius r r (fun _ => le_rfl) K f

theorem restrictRadius_trans (t : PositivePolyradius σ) (hts : ∀ i, t i ≤ s i)
    (f : GeneralizedTateAlgebra r K) :
    restrictRadius s t hts K (restrictRadius r s hsr K f) =
      restrictRadius r t (fun i => (hts i).trans (hsr i)) K f := by
  apply Subtype.ext
  exact (series_restrictRadius s t hts K (restrictRadius r s hsr K f)).trans
    ((series_restrictRadius r s hsr K f).trans
      (series_restrictRadius r t (fun i => (hts i).trans (hsr i)) K f).symm)

/-- Decreasing radii commutes with any radius-preserving variable inclusion. -/
theorem restrictRadius_rename {τ : Type w} (t q : PositivePolyradius τ)
    (hqt : ∀ j, q j ≤ t j) (e : σ ↪ τ)
    (ht : ∀ i, t (e i) = r i) (hq : ∀ i, q (e i) = s i)
    (f : GeneralizedTateAlgebra r K) :
    restrictRadius t q hqt K (rename r t e ht K f) =
      rename s q e hq K (restrictRadius r s hsr K f) := by
  apply Subtype.ext
  change series q K (restrictRadius t q hqt K (rename r t e ht K f)) =
    series q K (rename s q e hq K (restrictRadius r s hsr K f))
  simp only [series_restrictRadius, series_rename]

end GeneralCoefficients

section BoundedMaps

variable {σ : Type u} (r s : PositivePolyradius σ) (hsr : ∀ i, s i ≤ r i)
  (K : Type v) [NormedField K] [IsUltrametricDist K]

/-- The coefficient-preserving radius restriction as an actual bounded algebra map. -/
def boundedRestrictRadius :
    BoundedAlgHom K (GeneralizedTateAlgebra r K) (GeneralizedTateAlgebra s K) where
  toAlgHom := restrictRadius r s hsr K
  bounded := ⟨1, zero_lt_one, fun f => by
    change ‖restrictRadius r s hsr K f‖ ≤ 1 * ‖f‖
    rw [one_mul]
    exact norm_restrictRadius_le r s hsr K f⟩

@[simp] theorem boundedRestrictRadius_apply (f : GeneralizedTateAlgebra r K) :
    boundedRestrictRadius r s hsr K f = restrictRadius r s hsr K f := rfl

@[simp] theorem boundedRestrictRadius_self :
    boundedRestrictRadius r r (fun _ => le_rfl) K =
      BoundedAlgHom.id K (GeneralizedTateAlgebra r K) := by
  apply BoundedAlgHom.ext
  exact restrictRadius_self r K

theorem boundedRestrictRadius_trans (t : PositivePolyradius σ) (hts : ∀ i, t i ≤ s i) :
    (boundedRestrictRadius s t hts K).comp (boundedRestrictRadius r s hsr K) =
      boundedRestrictRadius r t (fun i => (hts i).trans (hsr i)) K := by
  apply BoundedAlgHom.ext
  exact restrictRadius_trans r s hsr K t hts

/-- Restriction commutes with the old-variable inclusion when only new radii shrink. -/
theorem boundedRestrictRadius_appendLeft {n m : ℕ} (r : PositivePolyradius (Fin n))
    (s t : PositivePolyradius (Fin m)) (hts : ∀ j, t j ≤ s j) :
    (boundedRestrictRadius (r.append s) (r.append t)
      (r.append_mono r s t (fun _ => le_rfl) hts) K).comp (appendLeft r s K) =
      appendLeft r t K := by
  apply BoundedAlgHom.ext
  intro f
  change restrictRadius (r.append s) (r.append t)
    (r.append_mono r s t (fun _ => le_rfl) hts) K
    (appendLeft r s K f) = appendLeft r t K f
  apply Subtype.ext
  change series (r.append t) K (restrictRadius (r.append s) (r.append t)
    (r.append_mono r s t (fun _ => le_rfl) hts) K
    (appendLeft r s K f)) = series (r.append t) K (appendLeft r t K f)
  rw [series_restrictRadius]
  exact (series_rename r (r.append s) (Fin.castAddEmb m)
    (fun i => PositivePolyradius.append_castAdd r s i) K f).trans
    (series_rename r (r.append t) (Fin.castAddEmb m)
      (fun i => PositivePolyradius.append_castAdd r t i) K f).symm

end BoundedMaps

end GeneralizedTateAlgebra

end Langlands.Analytic
