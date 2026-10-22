import Langlands.Geometry.Analytic.NoetherNormalization
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Ideal

/-! # Noetherianity of the actual finite-variable Tate algebras -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Finite-variable Tate algebras are Noetherian. The induction constructs
a distinguished element in each nonzero ideal and uses its actual finite
quotient; it does not assume Noetherianity of the analytic algebra. -/
theorem isNoetherianRing_tate (n : ℕ) :
    IsNoetherianRing (StrictTateAlgebra (Fin n) K) := by
  induction n with
  | zero =>
    exact isNoetherianRing_of_surjective K _
      (algebraMap K (StrictTateAlgebra (Fin 0) K))
      zeroVariables_algebraMap_surjective
  | succ n ih =>
    let := ih
    apply (isNoetherianRing_iff_ideal_fg _).mpr
    intro I
    by_cases hI : I = ⊥
    · subst I
      exact Submodule.fg_bot
    have hex : ∃ f, f ∈ I ∧ f ≠ 0 := by
      by_contra! hn
      apply hI
      apply le_antisymm _ bot_le
      intro f hf
      change f = 0
      exact hn f hf
    obtain ⟨f, hfI, hfzero⟩ := hex
    obtain ⟨φ, _, d, hdist⟩ := exists_distinguished_coordinateChange n f hfzero
    let e := φ.toRingEquiv.trans (regroupEquiv n)
    let S := RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K)
    let J : Ideal S := I.map e.toRingHom
    let w : S := e f
    let P : Ideal S := Ideal.span {w}
    have hwJ : w ∈ J := Ideal.mem_map_of_mem e.toRingHom hfI
    have hwP : w ∈ P := Ideal.subset_span (Set.mem_singleton w)
    have hPJ : P ≤ J := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hwJ)
    let : Module.Finite (StrictTateAlgebra (Fin n) K) (S ⧸ P) :=
      RestrictedSeries.finite_quotient_of_distinguished_mem P w d hdist hwP
    let : IsNoetherianRing (S ⧸ P) :=
      IsNoetherianRing.of_finite (StrictTateAlgebra (Fin n) K) (S ⧸ P)
    have hJ : J.FG := by
      apply Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective
        (f := Ideal.Quotient.mk P)
      · exact Ideal.fg_of_isNoetherianRing _
      · rw [Ideal.mk_ker, inf_eq_right.mpr hPJ]
        exact Submodule.fg_span_singleton w
      · exact Ideal.Quotient.mk_surjective
    have hback := hJ.map e.symm.toRingHom
    simpa only [J, RingEquiv.toRingHom_eq_coe, Ideal.map_of_equiv] using hback

instance (n : ℕ) : IsNoetherianRing (StrictTateAlgebra (Fin n) K) :=
  isNoetherianRing_tate n

end Langlands.Analytic.StrictTateAlgebra

namespace Langlands.Analytic.PresentedStrictAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Noetherianity descends through the actual Tate presentation map,
including the zero quotient. -/
instance (A : PresentedStrictAffinoidAlgebra K) : IsNoetherianRing A :=
  isNoetherianRing_of_surjective (StrictTateAlgebra (Fin A.arity) K) A
    (presentationMap K A).toAlgHom.toRingHom (presentationMap_surjective K A)

end Langlands.Analytic.PresentedStrictAffinoidAlgebra
