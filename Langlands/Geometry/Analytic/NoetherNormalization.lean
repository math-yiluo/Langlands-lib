import Langlands.Geometry.Analytic.TateFiniteReduction

/-! # Actual finite injective Tate maps for presented strict affinoid algebras -/

noncomputable section

universe u v

namespace Langlands.Analytic

namespace StrictTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- With no variables, every actual restricted series is constant. -/
theorem zeroVariables_algebraMap_surjective :
    Function.Surjective (algebraMap K (StrictTateAlgebra (Fin 0) K)) := by
  intro f
  obtain ⟨a, ha⟩ := MvPowerSeries.C_surjective f.val
  exact ⟨a, Subtype.ext ha⟩

variable {B : Type v} [NormedCommRing B] [Algebra K B] [Nontrivial B]

/-- The zero-variable base case uses only actual constants and the
injectivity of a unital field map into a nontrivial ring. -/
theorem zeroVariables_map_injective
    (h : StrictTateAlgebra (Fin 0) K →ₐ[K] B) : Function.Injective h := by
  intro f g hfg
  obtain ⟨a, rfl⟩ := zeroVariables_algebraMap_surjective f
  obtain ⟨b, rfl⟩ := zeroVariables_algebraMap_surjective g
  apply congrArg (algebraMap K (StrictTateAlgebra (Fin 0) K))
  apply (algebraMap K B).injective
  simpa only [h.commutes] using hfg

variable [CompleteSpace K]

/-- Starting with an actual finite bounded Tate map, construct a finite
injective bounded Tate map with at most as many variables. Induction replaces
each noninjective map by the proved smaller-variable finite map. -/
theorem exists_finite_injective_map (n : ℕ) :
    ∀ h : BoundedAlgHom K (StrictTateAlgebra (Fin n) K) B,
      h.toAlgHom.toRingHom.Finite →
      ∃ m ≤ n, ∃ g : BoundedAlgHom K (StrictTateAlgebra (Fin m) K) B,
        Function.Injective g ∧ g.toAlgHom.toRingHom.Finite := by
  induction n with
  | zero =>
    intro h hfinite
    exact ⟨0, le_rfl, h, zeroVariables_map_injective h.toAlgHom, hfinite⟩
  | succ n ih =>
    intro h hfinite
    by_cases hinj : Function.Injective h
    · exact ⟨n + 1, le_rfl, h, hinj, hfinite⟩
    · obtain ⟨h', hfinite'⟩ := exists_finite_smaller_map n h hfinite hinj
      obtain ⟨m, hm, g, hginj, hgfinite⟩ := ih h' hfinite'
      exact ⟨m, hm.trans (Nat.le_succ n), g, hginj, hgfinite⟩

end StrictTateAlgebra

namespace PresentedStrictAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Noether normalization for the genuine closed-ideal Tate quotient.
The output is an actual bounded scalar-compatible injective map whose
finite-module property is proved. It is not assumed in the presentation. -/
theorem exists_noetherNormalization (A : PresentedStrictAffinoidAlgebra K)
    [Nontrivial A] :
    ∃ m ≤ A.arity, ∃ g : BoundedAlgHom K (StrictTateAlgebra (Fin m) K) A,
      Function.Injective g ∧ g.toAlgHom.toRingHom.Finite := by
  apply StrictTateAlgebra.exists_finite_injective_map A.arity
    (presentationMap K A)
  exact RingHom.Finite.of_surjective _ (presentationMap_surjective K A)

end PresentedStrictAffinoidAlgebra

end Langlands.Analytic
