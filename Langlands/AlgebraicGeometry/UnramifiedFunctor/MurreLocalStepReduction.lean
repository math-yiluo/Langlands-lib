import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepParts
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreBaseChange
import Langlands.AlgebraicGeometry.Deformation.AdicCompletionNoetherian
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # The local step of Murre's induction from its parts

`murreLocalStep_of_parts` derives `MurreLocalStepStatement` from Steps 1, 2a and 2b
(`MurreLocalStepPartsStatement`). The induction hypothesis is applied to the punctured
spectra of `R` and of its completion `R̂` and to the artinian quotients of `R̂`; the lemmas
below bound the dimensions of their local rings. -/

universe u v

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

/-- The local rings of the punctured spectrum of a local noetherian ring `R` have smaller
Krull dimension than `R`. -/
theorem ringKrullDim_stalk_puncturedSpectrum_lt (R : CommRingCat.{u}) [IsLocalRing R]
    [IsNoetherianRing R] (s : (puncturedSpectrum R).toScheme) :
    ringKrullDim ((puncturedSpectrum R).toScheme.presheaf.stalk s) < ringKrullDim R := by
  rw [ringKrullDim_stalk_eq_coheight, ← coheight_eq_of_isOpenImmersion (puncturedSpectrum R).ι,
    ← idealHeight_eq_coheight, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have hs : (puncturedSpectrum R).ι s ≠ closedPoint R := s.2
  have : ((puncturedSpectrum R).ι s).asIdeal.IsPrime := ((puncturedSpectrum R).ι s).isPrime
  have hlt : ((puncturedSpectrum R).ι s).asIdeal < maximalIdeal R := by
    refine lt_of_le_of_ne (le_maximalIdeal ((puncturedSpectrum R).ι s).isPrime.ne_top) ?_
    intro h
    exact hs (PrimeSpectrum.ext h)
  exact_mod_cast Ideal.height_strict_mono_of_isPrime_of_isPrime hlt

/-- The local rings of the spectrum of an artinian ring have Krull dimension at most `0`. -/
theorem ringKrullDim_stalk_le_zero_of_isArtinianRing (A : CommRingCat.{u}) [IsArtinianRing A]
    (s : Spec A) : ringKrullDim ((Spec A).presheaf.stalk s) ≤ 0 := by
  rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight]
  have h0 : ringKrullDim A ≤ (0 : ℕ) := Ring.krullDimLE_iff.mp inferInstance
  have : s.asIdeal.IsPrime := s.isPrime
  exact (Ideal.height_le_ringKrullDim_of_isPrime (I := s.asIdeal)).trans (by exact_mod_cast h0)

/-- The completion `R̂` of a local noetherian ring `R` has Krull dimension at most that
of `R`. -/
theorem ringKrullDim_adicCompletion_le (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    ringKrullDim (AdicCompletion (maximalIdeal R) R) ≤ ringKrullDim R := by
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := AdicCompletion (maximalIdeal R) R),
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)]
  have : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R _)).symm⟩
  have h := Ideal.height_le_height_add_of_liesOver (maximalIdeal R)
    (maximalIdeal (AdicCompletion (maximalIdeal R) R))
  rw [← AdicCompletion.maximalIdeal_eq_map, Ideal.map_quotient_self, Ideal.height_bot,
    add_zero] at h
  exact_mod_cast h

/-- The quotient of a local noetherian ring by a power of its maximal ideal is artinian. -/
theorem isArtinianRing_quotient_maximalIdeal_pow (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (k : ℕ) : IsArtinianRing (A ⧸ maximalIdeal A ^ (k + 1)) :=
  IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _
    ⟨⟨inferInstance, Ideal.pow_le_self (Nat.succ_ne_zero k)⟩,
      fun _ hq _ ↦ haveI := hq.1; Ideal.IsPrime.le_of_pow_le hq.2⟩

/-- Under the induction hypothesis `MurreDimensionBound n`, the base change of `F` to the
punctured spectrum of a local noetherian ring of dimension `≤ n` is representable. -/
theorem unramifiedRepresentable_puncturedSpectrum {n : ℕ} (hn : MurreDimensionBound.{u, v} n)
    (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ n)
    (F : (Over (Spec R))ᵒᵖ ⥤ Type v) (hF : MurreConditions F) :
    UnramifiedRepresentable (baseChange (puncturedSpectrum R).ι F) :=
  hn _ _ (murreBaseChange _ _ _ F hF) fun s ↦
    (ringKrullDim_stalk_puncturedSpectrum_lt R s).trans_le hR

/-- Under the induction hypothesis `MurreDimensionBound n` with `n ≠ 0`, the criterion
holds over the spectrum of an artinian ring. -/
theorem unramifiedRepresentable_of_isArtinianRing {n : ℕ} (hn : MurreDimensionBound.{u, v} n)
    (hn0 : n ≠ 0) (A : CommRingCat.{u}) [IsArtinianRing A] (F : (Over (Spec A))ᵒᵖ ⥤ Type v)
    (hF : MurreConditions F) : UnramifiedRepresentable F :=
  hn _ F hF fun s ↦ (ringKrullDim_stalk_le_zero_of_isArtinianRing A s).trans_lt
    (by exact_mod_cast Nat.pos_of_ne_zero hn0)

/-- The local step of Murre's induction follows from Steps 1, 2a and 2b. -/
theorem murreLocalStep_of_parts (h : MurreLocalStepPartsStatement.{u, v}) :
    MurreLocalStepStatement.{u, v} := by
  obtain ⟨h1, h2a, h2b⟩ := h
  intro n hn R _ _ hR F hF
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr hR.le
    have : IsArtinianRing R := isArtinianRing_iff_krullDimLE_zero.mpr this
    exact h1 R F hF
  · have hdim : ringKrullDim (CommRingCat.of (AdicCompletion (maximalIdeal R) R)) ≤ n :=
      (ringKrullDim_adicCompletion_le R).trans hR.le
    have hF' : MurreConditions (baseChange (completionMap R) F) := murreBaseChange _ _ _ F hF
    refine h2b R F hF (unramifiedRepresentable_puncturedSpectrum hn R hR.le F hF) ?_
    refine h2a (CommRingCat.of (AdicCompletion (maximalIdeal R) R)) _ hF'
      (unramifiedRepresentable_puncturedSpectrum hn _ hdim _ hF') fun k ↦ ?_
    have := isArtinianRing_quotient_maximalIdeal_pow (AdicCompletion (maximalIdeal R) R) k
    exact unramifiedRepresentable_of_isArtinianRing hn hpos.ne' _ _
      (murreBaseChange _ _ _ _ hF')

end Langlands.AlgebraicGeometry.UnramifiedFunctor
