import Langlands.Geometry.Analytic.TateDistinguishedCoordinates
import Langlands.Geometry.Analytic.WeierstrassFinite

/-! # Decreasing the number of Tate variables in a finite map -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- The actual inclusion of the nonpivot variables, constructed by inverse
regrouping of constant restricted series. -/
def smallerVariables (n : ℕ) :
    BoundedAlgHom K (StrictTateAlgebra (Fin n) K)
      (StrictTateAlgebra (Fin (n + 1)) K) where
  toAlgHom :=
    { toRingHom := (regroupEquiv n).symm.toRingHom.comp
        (algebraMap (StrictTateAlgebra (Fin n) K)
          (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K)))
      commutes' := fun a => by
        apply (regroupEquiv n).injective
        change regroupEquiv n ((regroupEquiv n).symm _) =
          regroup (algebraMap K (StrictTateAlgebra (Fin (n + 1)) K) a)
        rw [RingEquiv.apply_symm_apply]
        exact (regroup_algebraMap n a).symm }
  bounded := by
    refine ⟨1, zero_lt_one, fun a => ?_⟩
    change ‖ungroup (algebraMap (StrictTateAlgebra (Fin n) K)
      (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K)) a)‖ ≤ 1 * ‖a‖
    rw [← norm_regroup, regroup_ungroup, norm_algebraMap, one_mul]

theorem norm_smallerVariables (n : ℕ) (a : StrictTateAlgebra (Fin n) K) :
    ‖smallerVariables n a‖ = ‖a‖ := by
  change ‖ungroup (algebraMap (StrictTateAlgebra (Fin n) K)
    (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K)) a)‖ = ‖a‖
  rw [← norm_regroup, regroup_ungroup, norm_algebraMap]

/-- Inclusion of the smaller Tate algebra in changed coordinates. The
inverse coordinate substitution is an actual isometric algebra map. -/
def smallerVariablesInCoordinates (n : ℕ)
    (φ : StrictTateAlgebra (Fin (n + 1)) K ≃ₐ[K]
      StrictTateAlgebra (Fin (n + 1)) K)
    (hφ : Isometry φ) :
    BoundedAlgHom K (StrictTateAlgebra (Fin n) K)
      (StrictTateAlgebra (Fin (n + 1)) K) where
  toAlgHom := φ.symm.toAlgHom.comp (smallerVariables n).toAlgHom
  bounded := by
    refine ⟨1, zero_lt_one, fun a => ?_⟩
    change ‖φ.symm (smallerVariables n a)‖ ≤ 1 * ‖a‖
    have heq := hφ.dist_eq (φ.symm (smallerVariables n a)) 0
    simp only [map_zero, AlgEquiv.apply_symm_apply, dist_zero_right] at heq
    rw [← heq, norm_smallerVariables, one_mul]

variable [CompleteSpace K]
variable {B : Type v} [NormedCommRing B] [Algebra K B]

/-- A noninjective finite bounded map from a Tate algebra can be replaced
by a finite bounded map from a Tate algebra with one fewer variable.
The killed nonzero series, coordinate change, and finite-module structure
are all obtained by proved constructions. -/
theorem exists_finite_smaller_map (n : ℕ)
    (h : BoundedAlgHom K (StrictTateAlgebra (Fin (n + 1)) K) B)
    (hfinite : h.toAlgHom.toRingHom.Finite)
    (hnoninj : ¬ Function.Injective h) :
    ∃ g : BoundedAlgHom K (StrictTateAlgebra (Fin n) K) B,
      g.toAlgHom.toRingHom.Finite := by
  classical
  have hex : ∃ f, f ≠ 0 ∧ h f = 0 := by
    by_contra hn
    apply hnoninj
    apply (injective_iff_map_eq_zero h.toAlgHom.toRingHom).mpr
    intro f hf
    by_contra hne
    exact hn ⟨f, hne, hf⟩
  obtain ⟨f, hf, hzero⟩ := hex
  obtain ⟨φ, hφ, d, hdist⟩ := exists_distinguished_coordinateChange n f hf
  let e := φ.toRingEquiv.trans (regroupEquiv n)
  let h' := h.toAlgHom.toRingHom.comp e.symm.toRingHom
  have hfinite' : h'.Finite := hfinite.comp e.symm.finite
  have hzero' : h' (regroupEquiv n (φ f)) = 0 := by
    change h (e.symm (e f)) = 0
    rw [RingEquiv.symm_apply_apply]
    exact hzero
  have hcoeff := RestrictedSeries.finite_coefficientMap_of_finite_of_distinguished_ker
    h' hfinite' (regroupEquiv n (φ f)) d hdist hzero'
  let g := h.comp (smallerVariablesInCoordinates n φ hφ)
  refine ⟨g, ?_⟩
  exact hcoeff

end Langlands.Analytic.StrictTateAlgebra
