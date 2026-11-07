import Langlands.Representation.Families.RenardFamilyStatements
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Renard VI.8.4 Theorem: finite projective modules are locally free

A proof of `LocalFreeCoverStatement` through Mathlib's free locus.
-/

namespace Langlands.Renard.AlgebraicFamily

universe uB uM

/-- VI.8.4 Theorem: a module over `B` is finitely generated and projective if and only if
finitely many elements generating the unit ideal give finite free localizations. -/
theorem localFreeCover : LocalFreeCoverStatement.{uB, uM} := by
  intro B _ _ _ _ _ M _ _
  constructor
  · rintro ⟨hfin, hproj⟩
    have : Module.FinitePresentation B M := Module.finitePresentation_of_projective B M
    let T : Set B := {r | Module.Finite (Localization.Away r) (LocalizedModule.Away r M) ∧
      Module.Free (Localization.Away r) (LocalizedModule.Away r M)}
    have hT : Ideal.span T = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hTm⟩ := Ideal.exists_le_maximal _ hne
      have : Module.Free (Localization.AtPrime m) (LocalizedModule m.primeCompl M) :=
        Module.free_of_flat_of_isLocalRing
      obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
        m.primeCompl (LocalizedModule.mkLinearMap m.primeCompl M) (Localization.AtPrime m)
      exact hr (hTm (Ideal.subset_span ⟨inferInstance, hfree⟩))
    obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite T).mp hT
    refine ⟨s.card, fun i => (s.equivFin.symm i).val, ?_,
      fun i => hsT (s.equivFin.symm i).property⟩
    have hrange : Set.range (fun i => (s.equivFin.symm i).val) = (s : Set B) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (s.equivFin.symm i).property
      · intro hx
        exact ⟨s.equivFin ⟨x, hx⟩, by simp⟩
    rw [hrange, hs]
  · rintro ⟨r, f, hspan, hf⟩
    have hfin : Module.Finite B M := by
      apply Module.Finite.of_localizationSpan (Set.range f) hspan
      rintro ⟨_, i, rfl⟩
      exact (hf i).1
    have : Module.FinitePresentation B M := Module.finitePresentation_of_finite B M
    refine ⟨hfin, ?_⟩
    rw [← Module.freeLocus_eq_univ_iff]
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨i, hi⟩ : ∃ i, f i ∉ p.asIdeal := by
      by_contra h
      push Not at h
      apply p.isPrime.ne_top
      rw [eq_top_iff, ← hspan, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact h i
    have : Module.Free (Localization.Away (f i)) (LocalizedModule.Away (f i) M) := (hf i).2
    exact (Module.basicOpen_subset_freeLocus_iff.mpr inferInstance) hi

end Langlands.Renard.AlgebraicFamily
