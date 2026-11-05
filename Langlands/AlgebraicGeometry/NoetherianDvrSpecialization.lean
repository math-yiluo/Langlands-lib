import Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates
import Mathlib.AlgebraicGeometry.Noetherian

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

/-- An actual DVR-valued point with prescribed generic and closed images. -/
structure DvrSpecialization (X : Scheme.{u}) (η s : X) where
  ring : CommRingCat.{u}
  [domain : IsDomain ring]
  [dvr : IsDiscreteValuationRing ring]
  map : Spec ring ⟶ X
  generic_image : map (⟨⊥, inferInstance⟩ : PrimeSpectrum ring) = η
  closed_image : map (IsLocalRing.closedPoint ring) = s

attribute [instance] DvrSpecialization.domain DvrSpecialization.dvr

/-- Two distinct comparable primes of a Noetherian ring are the endpoint images
of an actual DVR-valued point. -/
theorem nonempty_dvrSpecialization_spec
    (C : Type u) [CommRing C] [IsNoetherianRing C]
    (η s : PrimeSpectrum C) (hle : η.asIdeal ≤ s.asIdeal) (hne : η ≠ s) :
    Nonempty (DvrSpecialization (Spec (CommRingCat.of C)) η s) := by
  classical
  let D := C ⧸ η.asIdeal
  let P : Ideal D := s.asIdeal.map (Ideal.Quotient.mk η.asIdeal)
  have hP : P.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)
  have hPcomap : P.comap (Ideal.Quotient.mk η.asIdeal) = s.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hle]
  have hPne : P ≠ ⊥ := by
    intro h
    apply hne
    apply PrimeSpectrum.ext
    rw [← hPcomap, h, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  let B := Localization.AtPrime P
  let K := FractionRing D
  have hBfield : ¬ IsField B := by
    intro hF
    apply hPne
    rw [← Localization.AtPrime.under_maximalIdeal (I := P), Ideal.under_def,
      IsLocalRing.isField_iff_maximalIdeal_eq.mp hF,
      Ideal.comap_bot_of_injective _ (IsLocalization.injective B P.primeCompl_le_nonZeroDivisors)]
  obtain ⟨V, hV, hBV, hdom⟩ :=
    IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates (R := B) hBfield K
  have := hV
  let φ₀ : C →+* K :=
    (algebraMap B K).comp ((algebraMap D B).comp (Ideal.Quotient.mk η.asIdeal))
  let φ : C →+* ↥V := φ₀.codRestrict V.toSubring (fun x => hBV _)
  have hφ₀ : RingHom.ker φ₀ = η.asIdeal := by
    rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_comap, ← Ideal.comap_comap,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective B K),
      Ideal.comap_bot_of_injective _ (IsLocalization.injective B P.primeCompl_le_nonZeroDivisors),
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hφ : RingHom.ker φ = η.asIdeal := by
    calc
      RingHom.ker φ = RingHom.ker φ₀ := by
        ext x
        rw [RingHom.mem_ker, RingHom.mem_ker, ← Subtype.val_inj]
        rfl
      _ = η.asIdeal := hφ₀
  refine ⟨{
    ring := CommRingCat.of ↥V
    map := Spec.map (CommRingCat.ofHom φ)
    generic_image := ?_
    closed_image := ?_ }⟩
  · apply PrimeSpectrum.ext
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom]
    exact hφ
  · apply PrimeSpectrum.ext
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom]
    calc
      Ideal.comap φ (IsLocalRing.maximalIdeal ↥V) =
          P.comap (Ideal.Quotient.mk η.asIdeal) := by
        ext x
        rw [Ideal.mem_comap, Ideal.mem_comap]
        rw [← ValuationSubring.coe_mem_nonunits_iff]
        change algebraMap B K (algebraMap D B (Ideal.Quotient.mk η.asIdeal x)) ∈ V.nonunits ↔ _
        rw [← hdom, IsLocalization.AtPrime.to_map_mem_maximal_iff B P]
      _ = s.asIdeal := hPcomap

/-- Every strict specialization in a locally Noetherian scheme is realized by
an actual DVR-valued point, without a dimension or adjacency restriction. -/
theorem nonempty_dvrSpecialization
    (X : Scheme.{u}) [IsLocallyNoetherian X] (η s : X)
    (hspec : η ⤳ s) (hne : η ≠ s) : Nonempty (DvrSpecialization X η s) := by
  classical
  obtain ⟨U, hU, hsU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) (by trivial)
  have hηU := hspec.mem_open U.isOpen hsU
  obtain ⟨η', hη'⟩ : η ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hηU
  obtain ⟨s', hs'⟩ : s ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hsU
  have hspec' : η' ⤳ s' := by
    apply hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp
    rwa [hη', hs']
  have hne' : η' ≠ s' := by
    intro h
    exact hne (hη'.symm.trans ((congrArg hU.fromSpec h).trans hs'))
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨M⟩ := nonempty_dvrSpecialization_spec Γ(X, U) η' s'
    ((PrimeSpectrum.le_iff_specializes _ _).mpr hspec') hne'
  refine ⟨{
    ring := M.ring
    map := M.map ≫ hU.fromSpec
    generic_image := ?_
    closed_image := ?_ }⟩
  · rw [Scheme.Hom.comp_apply, M.generic_image]
    exact hη'
  · rw [Scheme.Hom.comp_apply, M.closed_image]
    exact hs'

end Langlands.AlgebraicGeometry
