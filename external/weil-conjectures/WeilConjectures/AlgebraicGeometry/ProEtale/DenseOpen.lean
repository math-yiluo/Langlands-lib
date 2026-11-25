/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.AlgebraicGeometry.NormalEtale
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.RingTheory.ProEtale.RegularLocalization

/-!
# Weakly étale schemes over a regular scheme and dense opens

We collect the point-set facts about a scheme `W` weakly étale over a regular scheme `C` used to
show that the sections of the constant `ℓ`-adic sheaf over `W` are determined by, and extend
uniquely from, the preimage of a dense open of `C`.

## Main statements

- `PrimeSpectrum.exists_specializes_of_mem_closure_of_isCompact`: a point in the closure of a
  quasi-compact open subset of `Spec R` is a specialization of one of its points.
- `AlgebraicGeometry.Scheme.exists_specializes_of_mem_closure`: the same near an affine open of a
  scheme.
- `AlgebraicGeometry.Scheme.exists_specializes_and_specializes_of_isDomain_stalk`: two
  generizations of a point with integral local ring have a common generization.
- `AlgebraicGeometry.isDomain_stalk_of_weaklyEtale`: a scheme weakly étale over a scheme with
  regular local rings has integral local rings.
- `AlgebraicGeometry.isDomain_stalk_of_weaklyEtale_of_isIntegrallyClosed`: a scheme weakly étale
  over a scheme whose local rings are integrally closed domains has integral local rings.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace PrimeSpectrum

variable {R : Type*} [CommRing R]

/-- A prime in the closure of the basic open `D(f)` contains a prime not containing `f`:
otherwise `f` is nilpotent in `R_p`, so `s f ^ n = 0` for some `s ∉ p`, and `D(s)` is a
neighbourhood of `p` disjoint from `D(f)`. -/
lemma exists_specializes_of_mem_closure_basicOpen {f : R} {p : PrimeSpectrum R}
    (h : p ∈ closure (basicOpen f : Set (PrimeSpectrum R))) :
    ∃ q ∈ (basicOpen f : Set (PrimeSpectrum R)), q ⤳ p := by
  by_contra hne
  push Not at hne
  have hnil : IsNilpotent (algebraMap R (Localization.AtPrime p.asIdeal) f) := by
    rw [← mem_nilradical, nilradical_eq_sInf]
    refine Submodule.mem_sInf.2 fun Q hQ ↦ ?_
    have hQ' : Ideal.IsPrime Q := hQ
    let Q' : PrimeSpectrum (Localization.AtPrime p.asIdeal) := ⟨Q, hQ'⟩
    have hle : comap (algebraMap R (Localization.AtPrime p.asIdeal)) Q' ≤ p := by
      have hmem : comap (algebraMap R (Localization.AtPrime p.asIdeal)) Q' ∈
          Set.range (comap (algebraMap R (Localization.AtPrime p.asIdeal))) := ⟨Q', rfl⟩
      rw [localization_comap_range (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl] at hmem
      intro r hr
      by_contra hrp
      exact Set.disjoint_left.1 hmem (show r ∈ p.asIdeal.primeCompl from hrp) hr
    by_contra hf
    exact hne _ hf ((le_iff_specializes _ _).1 hle)
  obtain ⟨n, hn⟩ := hnil
  rw [← map_pow, IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl] at hn
  obtain ⟨⟨s, hs⟩, hsf⟩ := hn
  obtain ⟨q, hqs, hqf⟩ := mem_closure_iff.1 h (basicOpen s) (basicOpen s).isOpen hs
  exact q.isPrime.mul_notMem hqs (fun hq ↦ hqf (q.isPrime.mem_of_pow_mem n hq))
    (hsf ▸ q.asIdeal.zero_mem)

/-- A prime in the closure of a quasi-compact open subset `Z` of `Spec R` is a specialization of
a point of `Z`: `Z` is a finite union of basic opens. -/
lemma exists_specializes_of_mem_closure_of_isCompact {Z : Set (PrimeSpectrum R)} (hZ : IsOpen Z)
    (hZc : IsCompact Z) {p : PrimeSpectrum R} (h : p ∈ closure Z) : ∃ q ∈ Z, q ⤳ p := by
  obtain ⟨t, ht, rfl⟩ := (isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis
    (fun r : R ↦ (basicOpen r : Set (PrimeSpectrum R))) isTopologicalBasis_basic_opens
    isCompact_basicOpen Z).1 ⟨hZc, hZ⟩
  rw [ht.closure_biUnion] at h
  obtain ⟨r, hr, hpr⟩ := Set.mem_iUnion₂.1 h
  obtain ⟨q, hq, hqp⟩ := exists_specializes_of_mem_closure_basicOpen hpr
  exact ⟨q, Set.mem_iUnion₂.2 ⟨r, hr, hq⟩, hqp⟩

end PrimeSpectrum

namespace AlgebraicGeometry

namespace Scheme

/-- A point `x` in the closure of an open subset `Z` of a scheme is a specialization of a point
of `Z`, provided `x` has an affine open neighbourhood `N` with `Z ∩ N` quasi-compact. -/
theorem exists_specializes_of_mem_closure {X : Scheme.{u}} {Z : Set X} (hZ : IsOpen Z) {x : X}
    {N : X.Opens} (hN : IsAffineOpen N) (hxN : x ∈ N) (hc : IsCompact (Z ∩ N))
    (hx : x ∈ closure Z) : ∃ z ∈ Z, z ⤳ x := by
  let e := hN.fromSpec
  have he : IsOpenEmbedding e := e.isOpenEmbedding
  have hrange : Set.range e = N := hN.range_fromSpec
  obtain ⟨p, rfl⟩ : x ∈ Set.range e := hrange ▸ hxN
  have himage : e '' (e ⁻¹' Z) = Z ∩ N := by
    rw [Set.image_preimage_eq_inter_range, hrange]
  have hsc : IsCompact (e ⁻¹' Z) := by
    rw [he.isInducing.isCompact_iff, himage]
    exact hc
  have hps : p ∈ closure (e ⁻¹' Z) := by
    rw [he.isInducing.closure_eq_preimage_closure_image, himage, Set.mem_preimage,
      Set.inter_comm]
    exact N.isOpen.inter_closure ⟨hxN, hx⟩
  obtain ⟨q, hq, hqp⟩ :=
    PrimeSpectrum.exists_specializes_of_mem_closure_of_isCompact (hZ.preimage e.continuous) hsc hps
  exact ⟨e q, hq, hqp.map e.continuous⟩

/-- **Generizations of a point with integral local ring are directed.** If the local ring of `X`
at `x` is a domain, any two generizations of `x` are specializations of the image of the generic
point of `Spec 𝒪_{X,x}`. -/
theorem exists_specializes_and_specializes_of_isDomain_stalk {X : Scheme.{u}} {x : X}
    (hx : IsDomain (X.presheaf.stalk x)) {y₁ y₂ : X} (h₁ : y₁ ⤳ x) (h₂ : y₂ ⤳ x) :
    ∃ z, z ⤳ y₁ ∧ z ⤳ y₂ := by
  have hr : ∀ y, y ⤳ x → ∃ p, X.fromSpecStalk x p = y := fun y hy ↦ by
    have : y ∈ Set.range (X.fromSpecStalk x) := by rw [range_fromSpecStalk]; exact hy
    exact this
  obtain ⟨p₁, rfl⟩ := hr y₁ h₁
  obtain ⟨p₂, rfl⟩ := hr y₂ h₂
  let ξ : PrimeSpectrum (X.presheaf.stalk x) := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨X.fromSpecStalk x ξ, ?_, ?_⟩
  · exact (((PrimeSpectrum.le_iff_specializes ξ p₁).1 bot_le).map
      (X.fromSpecStalk x).continuous)
  · exact (((PrimeSpectrum.le_iff_specializes ξ p₂).1 bot_le).map
      (X.fromSpecStalk x).continuous)

end Scheme

/-- **Weakly étale schemes over regular schemes have integral local rings.** If the local rings
of `C` are regular and `f : W ⟶ C` is weakly étale, then the local rings of `W` are domains
(`Algebra.WeaklyEtale.isDomain_localization_of_isRegularLocalRing`). -/
theorem isDomain_stalk_of_weaklyEtale {W C : Scheme.{u}} (f : W ⟶ C) [WeaklyEtale f]
    (hC : ∀ c : C, IsRegularLocalRing (C.presheaf.stalk c)) (w : W) :
    IsDomain (W.presheaf.stalk w) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hwU, -⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f w)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, hVU⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (show w ∈ f ⁻¹ᵁ U from hwU)
      (f ⁻¹ᵁ U).isOpen
  have hφ := HasRingHomProperty.appLE @WeaklyEtale f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  algebraize [(f.appLE U V hVU).hom]
  let := W.presheaf.algebra_section_stalk ⟨w, hwV⟩
  have := hV.isLocalization_stalk ⟨w, hwV⟩
  set P := (hV.primeIdealOf ⟨w, hwV⟩).asIdeal
  have := Algebra.WeaklyEtale.isDomain_localization_of_isRegularLocalRing (R := Γ(C, U))
    (fun p _ ↦ hU.isRegularLocalRing_localization (fun c _ ↦ hC c) p) P
  exact (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
    (W.presheaf.stalk w)).toMulEquiv.symm.isDomain

/-- **Weakly étale schemes over normal schemes have integral local rings.** If the local rings of
`C` are integrally closed domains and `f : W ⟶ C` is weakly étale, then the local rings of `W`
are domains (`Algebra.WeaklyEtale.isDomain_localization_of_isIntegrallyClosed`). -/
theorem isDomain_stalk_of_weaklyEtale_of_isIntegrallyClosed {W C : Scheme.{u}} (f : W ⟶ C)
    [WeaklyEtale f]
    (hC : ∀ c : C, IsDomain (C.presheaf.stalk c) ∧ IsIntegrallyClosed (C.presheaf.stalk c))
    (w : W) : IsDomain (W.presheaf.stalk w) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hwU, -⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f w)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, hVU⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (show w ∈ f ⁻¹ᵁ U from hwU)
      (f ⁻¹ᵁ U).isOpen
  have hφ := HasRingHomProperty.appLE @WeaklyEtale f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  algebraize [(f.appLE U V hVU).hom]
  let := W.presheaf.algebra_section_stalk ⟨w, hwV⟩
  have := hV.isLocalization_stalk ⟨w, hwV⟩
  set P := (hV.primeIdealOf ⟨w, hwV⟩).asIdeal
  have := Algebra.WeaklyEtale.isDomain_localization_of_isIntegrallyClosed (R := Γ(C, U))
    (fun p _ ↦ hU.isDomain_and_isIntegrallyClosed_localization (fun c _ ↦ hC c) p) P
  exact (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
    (W.presheaf.stalk w)).toMulEquiv.symm.isDomain

end AlgebraicGeometry
