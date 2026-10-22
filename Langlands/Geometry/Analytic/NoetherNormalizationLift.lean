import Langlands.Geometry.Analytic.NoetherNormalization

/-! # Retaining the actual ambient embedding in Noether normalization -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {B : Type v} [NormedCommRing B] [Algebra K B]

/-- The smaller-variable finite map is obtained through an actual
Gauss-isometric embedding in the original Tate algebra. -/
theorem exists_finite_smaller_embedding (n : ℕ)
    (h : BoundedAlgHom K (StrictTateAlgebra (Fin (n + 1)) K) B)
    (hfinite : h.toAlgHom.toRingHom.Finite)
    (hnoninj : ¬ Function.Injective h) :
    ∃ g : BoundedAlgHom K (StrictTateAlgebra (Fin n) K)
      (StrictTateAlgebra (Fin (n + 1)) K),
      (∀ a, ‖g a‖ = ‖a‖) ∧ (h.comp g).toAlgHom.toRingHom.Finite := by
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
  refine ⟨smallerVariablesInCoordinates n φ hφ, ?_, ?_⟩
  · intro a
    change ‖φ.symm (smallerVariables n a)‖ = ‖a‖
    have heq := hφ.dist_eq (φ.symm (smallerVariables n a)) 0
    simp only [map_zero, AlgEquiv.apply_symm_apply, dist_zero_right] at heq
    rw [← heq, norm_smallerVariables]
  · exact RestrictedSeries.finite_coefficientMap_of_finite_of_distinguished_ker
      h' hfinite' (regroupEquiv n (φ f)) d hdist hzero'

variable [Nontrivial B]

/-- Construct the normalization through a norm-preserving map into the
original Tate algebra, so its coefficients can later be lifted through
further quotient maps with the same unit-ball bound. -/
theorem exists_normalizing_embedding (n : ℕ) :
    ∀ h : BoundedAlgHom K (StrictTateAlgebra (Fin n) K) B,
      h.toAlgHom.toRingHom.Finite →
      ∃ m ≤ n, ∃ g : BoundedAlgHom K (StrictTateAlgebra (Fin m) K)
        (StrictTateAlgebra (Fin n) K),
        (∀ a, ‖g a‖ = ‖a‖) ∧ Function.Injective (h.comp g) ∧
          (h.comp g).toAlgHom.toRingHom.Finite := by
  induction n with
  | zero =>
      intro h hfinite
      exact ⟨0, le_rfl, BoundedAlgHom.id K _, fun _ => rfl,
        zeroVariables_map_injective h.toAlgHom, hfinite⟩
  | succ n ih =>
      intro h hfinite
      by_cases hinj : Function.Injective h
      · exact ⟨n + 1, le_rfl, BoundedAlgHom.id K _, fun _ => rfl, hinj, hfinite⟩
      · obtain ⟨g, hgnorm, hgfinite⟩ :=
          exists_finite_smaller_embedding n h hfinite hinj
        obtain ⟨m, hm, e, henorm, heinj, hefinite⟩ := ih (h.comp g) hgfinite
        refine ⟨m, hm.trans (Nat.le_succ n), g.comp e, ?_, heinj, hefinite⟩
        intro a
        change ‖g (e a)‖ = ‖a‖
        rw [hgnorm, henorm]

end Langlands.Analytic.StrictTateAlgebra
