import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Langlands.CommutativeAlgebra.IntegralFibre.GenericSmoothness

/-! # A smooth faithfully flat cover with free differentials

Let `S` be a flat finitely presented `R`-algebra such that `K ⊗[R] S` is a domain for every field
`K` over `R`. Then there are finitely many `s i : S` such that each `S_{s i}` is smooth over `R`
with free module of differentials, and `∀ i, S_{s i}` is faithfully flat over `R`. -/

universe u

open TensorProduct

namespace Langlands.CommutativeAlgebra

/-- If `M_r` is free over `A_r`, then `M_{r t}` is free over `A_{r t}`. -/
theorem free_localizedModule_away_mul {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (r t : A) [Module.Free (Localization.Away r) (LocalizedModule.Away r M)] :
    Module.Free (Localization.Away (r * t)) (LocalizedModule.Away (r * t) M) := by
  let Ar := Localization.Away r
  let P := Localization.Away (r * t)
  let : Algebra Ar P := (IsLocalization.Away.awayToAwayRight (S := Ar) (P := P) r t).toAlgebra
  have : IsScalarTower A Ar P :=
    .of_algebraMap_eq fun a ↦ (IsLocalization.Away.awayToAwayRight_eq (S := Ar) (P := P) r t a).symm
  have : Module.Free Ar (Ar ⊗[A] M) := .of_equiv (LocalizedModule.equivTensorProduct _ M)
  have : Module.Free P (P ⊗[A] M) :=
    .of_equiv (AlgebraTensorModule.cancelBaseChange A Ar P P M)
  exact .of_equiv (LocalizedModule.equivTensorProduct _ M).symm

/-- Every point `q` of the smooth locus of a finitely presented algebra lies in a basic open
`D(s)` such that `S_s` is smooth with free module of differentials. -/
theorem exists_notMem_smooth_free {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (q : PrimeSpectrum S) (hq : q ∈ Algebra.smoothLocus R S) :
    ∃ s ∉ q.asIdeal, Algebra.Smooth R (Localization.Away s) ∧
      Module.Free (Localization.Away s) (Ω[Localization.Away s⁄R]) := by
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hqg, hg⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hq Algebra.isOpen_smoothLocus
  have : Module.Free (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl Ω[S⁄R]) :=
    (Algebra.smoothLocus_eq_compl_support_inter.le hq).2
  obtain ⟨r, hr, hr', -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    q.asIdeal.primeCompl (LocalizedModule.mkLinearMap q.asIdeal.primeCompl Ω[S⁄R])
    (Localization.AtPrime q.asIdeal)
  refine ⟨r * g, q.2.mul_notMem hr hqg, ?_, ?_⟩
  · rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth]
    exact (SetLike.coe_subset_coe.mpr (PrimeSpectrum.basicOpen_mul_le_right r g)).trans hg
  · have := free_localizedModule_away_mul r g (M := Ω[S⁄R])
    exact .of_equiv ((IsLocalizedModule.iso (.powers (r * g))
      (KaehlerDifferential.map R R S (Localization.Away (r * g)))).extendScalarsOfIsLocalization
        (.powers (r * g)) (Localization.Away (r * g)))

/-- **Smooth cover.** Let `S` be a flat finitely presented `R`-algebra such that `K ⊗[R] S` is a
domain for every field `K` over `R`. Then there are finitely many `s i : S` such that each
`S_{s i}` is smooth over `R` with free module of differentials, and `∀ i, S_{s i}` is
faithfully flat over `R`. -/
theorem exists_smooth_free_cover {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (hS : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (K ⊗[R] S)) :
    ∃ (m : ℕ) (s : Fin m → S), (∀ i, Algebra.Smooth R (Localization.Away (s i))) ∧
      (∀ i, Module.Free (Localization.Away (s i)) (Ω[Localization.Away (s i)⁄R])) ∧
      Module.FaithfullyFlat R (∀ i, Localization.Away (s i)) := by
  -- Over each prime `p` of `R`, a basic open `D(f p)` of `Spec S` meeting the fibre over `p`.
  have H (p : PrimeSpectrum R) : ∃ f : S, (Algebra.Smooth R (Localization.Away f) ∧
      Module.Free (Localization.Away f) (Ω[Localization.Away f⁄R])) ∧
      p ∈ PrimeSpectrum.comap (algebraMap R S) '' (PrimeSpectrum.basicOpen f) := by
    obtain ⟨q, hq, rfl⟩ := exists_mem_smoothLocus_comap_eq hS p
    obtain ⟨f, hf, h₁, h₂⟩ := exists_notMem_smooth_free q hq
    exact ⟨f, ⟨h₁, h₂⟩, q, hf, rfl⟩
  choose f hf hpf using H
  -- The images of the `D(f p)` are open, so finitely many of them cover `Spec R`.
  have hopen (p : PrimeSpectrum R) :
      IsOpen (PrimeSpectrum.comap (algebraMap R S) '' (PrimeSpectrum.basicOpen (f p))) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation _
      (PrimeSpectrum.basicOpen (f p)).2
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen
    fun p _ ↦ Set.mem_iUnion.mpr ⟨p, hpf p⟩
  let e := t.equivFin
  let s : Fin t.card → S := fun i ↦ f (e.symm i)
  refine ⟨t.card, s, fun i ↦ (hf _).1, fun i ↦ (hf _).2, ?_⟩
  have (i : Fin t.card) : Module.Flat R (Localization.Away (s i)) := .trans R S _
  have : Module.Flat R (∀ i, Localization.Away (s i)) :=
    .of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := R)).symm
  refine .of_comap_surjective fun p ↦ ?_
  obtain ⟨p', hp't, q, hq, rfl⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
  let i := e ⟨p', hp't⟩
  have hi : s i = f p' := by simp [s, i]
  obtain ⟨Q, rfl⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away (s i)))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ (s i), hi]
    exact hq
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom _ i) Q, ?_⟩
  ext1
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.comap_comap]
  congr 1

end Langlands.CommutativeAlgebra
