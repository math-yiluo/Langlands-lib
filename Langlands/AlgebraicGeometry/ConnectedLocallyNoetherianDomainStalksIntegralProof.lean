import Langlands.AlgebraicGeometry.ConnectedLocallyNoetherianDomainStalksIntegralStatement
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Integrality from connectedness, local Noetherianity, and domain stalks

Finite generation of the kernel of a prime localization gives irreducible open
neighborhoods. These make all global irreducible components open.
-/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace Langlands.AlgebraicGeometry

private lemma exists_domain_away
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [IsDomain (Localization.AtPrime p)] :
    ∃ f : R, f ∉ p ∧ IsDomain (Localization.Away f) := by
  classical
  let g : R →+* Localization.AtPrime p := algebraMap R _
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing (RingHom.ker g))
  have hzero (i : Fin n) : g (a i) = 0 := by
    exact (show a i ∈ RingHom.ker g from
      ha ▸ Submodule.subset_span (Set.mem_range_self i))
  choose s hs using fun i => (IsLocalization.map_eq_zero_iff p.primeCompl
    (Localization.AtPrime p) (a i)).mp (hzero i)
  let f : R := ∏ i, (s i : R)
  have hfp : f ∉ p := by
    exact p.primeCompl.prod_mem fun i _ => (s i).property
  have hfa (i : Fin n) : f * a i = 0 := by
    obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem (fun j : Fin n => (s j : R))
      (Finset.mem_univ i)
    rw [show f = (s i : R) * b from hb, mul_assoc, mul_comm b,
      ← mul_assoc, hs i, zero_mul]
  have hker : RingHom.ker g ≤ RingHom.ker (algebraMap R (Localization.Away f)) := by
    rw [← ha]
    apply Submodule.span_le.mpr
    rintro b ⟨i, rfl⟩
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f)
      (Localization.Away f) (a i)).mpr
      ⟨⟨f, Submonoid.mem_powers f⟩, hfa i⟩
  have hg : g f ≠ 0 :=
    (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hfp⟩ : p.primeCompl)).ne_zero
  have : IsDomain (Localization.Away (g f)) := Localization.Away.isDomain hg
  refine ⟨f, hfp, Function.Injective.isDomain (Localization.awayMap g f) ?_⟩
  apply (Localization.awayMap_injective_iff).mpr
  intro b hb
  have h := hker hb
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f)
    (Localization.Away f) b).mp h
  exact ⟨m, hm⟩

private lemma exists_irreducible_open :
    ∀ (X : Scheme.{u}) (x : X), IsLocallyNoetherian X →
      IsDomain (X.presheaf.stalk x) →
      ∃ U : X.Opens, x ∈ U ∧ IsIrreducible (U : Set X) := by
  apply reduce_to_affine_nbhd
    (fun X x => IsLocallyNoetherian X → IsDomain (X.presheaf.stalk x) →
      ∃ U : X.Opens, x ∈ U ∧ IsIrreducible (U : Set X))
  · intro R p hN hD
    have : p.asIdeal.IsPrime := p.isPrime
    have : IsNoetherianRing R := isLocallyNoetherian_Spec.mp hN
    have : IsDomain (Localization.AtPrime p.asIdeal) :=
      (Spec.stalkIso R p).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
    obtain ⟨f, hf, hdom⟩ := exists_domain_away R p.asIdeal
    refine ⟨PrimeSpectrum.basicOpen f, hf, ?_⟩
    change IsIrreducible (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (PrimeSpectrum (Localization.Away f))).image
        _ (PrimeSpectrum.continuous_comap _).continuousOn
  · intro X Y f _ x hx hN hD
    have hNx : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion f
    have hDx : IsDomain (X.presheaf.stalk x) :=
      (asIso (f.stalkMap x)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
    obtain ⟨U, hxU, hU⟩ := hx hNx hDx
    refine ⟨f ''ᵁ U, ⟨x, hxU, rfl⟩, ?_⟩
    exact hU.image f f.continuous.continuousOn

private lemma isOpen_irreducible_component {T : Type u} [TopologicalSpace T]
    (h : ∀ x : T, ∃ U : Opens T, x ∈ U ∧ IsIrreducible (U : Set T))
    (C : Set T) (hC : C ∈ irreducibleComponents T) : IsOpen C := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hxU, hU⟩ := h x
  obtain ⟨D, hD, hUD⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (U : Set T) hU
  have hCD : C ⊆ D :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 U.isOpen
      ⟨x, hx, hxU⟩).trans
      (closure_minimal (Set.inter_subset_right.trans hUD)
        (isClosed_of_mem_irreducibleComponents D hD))
  exact ⟨U, hUD.trans (hC.2 hD.1 hCD), U.isOpen, hxU⟩

/-- A connected locally Noetherian scheme with domain stalks is integral. -/
theorem connectedLocallyNoetherianDomainStalksIntegral :
    ConnectedLocallyNoetherianDomainStalksIntegral.{u} := by
  intro X hN hconn hD
  have hlocal (x : X) : ∃ U : X.Opens, x ∈ U ∧ IsIrreducible (U : Set X) :=
    exists_irreducible_open X x hN (hD x)
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hclosed : IsClosed (irreducibleComponent x) :=
    isClosed_of_mem_irreducibleComponents _ hC
  have hopen : IsOpen (irreducibleComponent x) :=
    isOpen_irreducible_component hlocal _ hC
  have heq : irreducibleComponent x = Set.univ :=
    (show IsClopen (irreducibleComponent x) from ⟨hclosed, hopen⟩).eq_univ hC.1.nonempty
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr (by
    simpa only [heq, Set.top_eq_univ] using hC.1)
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := hD x
    infer_instance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end Langlands.AlgebraicGeometry
