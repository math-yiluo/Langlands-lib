/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Affine opens of one-dimensional schemes

Let `W` be a locally noetherian scheme of dimension at most one and `O ⊆ W` an open subset.
Every point of `W` has an affine open neighbourhood `V` such that `V ∩ O` is again affine
(`AlgebraicGeometry.Scheme.exists_isAffineOpen_inf_isAffineOpen`). In fact `V` and `V ∩ O` can be
taken to be basic opens `D(g)` and `D(g f)` of an affine open: this is the commutative algebra
statement `PrimeSpectrum.exists_basicOpen_inter_compl_zeroLocus_eq`, proved by prime avoidance.
Write `Z = V(I)` for the complement of `O`. If `x ∈ Z`, choose `f ∈ I` outside the minimal primes
not containing `I`; then `V(f) ∖ Z` consists of the finitely many primes minimal over `(f)`
which do not contain `I`, all of them maximal and different from `x`, and `g` is chosen in all
of them but not in `x`.

This is used to compute higher direct images along open immersions into curves locally by affine
schemes (`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CurveOpenDirectImage`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace PrimeSpectrum

variable {A : Type*} [CommRing A]

/-- In a ring of Krull dimension at most one, a prime ideal strictly contained in another one is
minimal. -/
lemma isMin_of_lt_of_ringKrullDim_le_one (hA : ringKrullDim A ≤ 1) {p q : PrimeSpectrum A}
    (h : p < q) : IsMin p := by
  have := Order.krullDim_le_one_iff.1 hA p
  exact this.resolve_right fun hp ↦ absurd (hp h.le) h.not_ge

/-- A minimal point of the prime spectrum is a minimal prime of the ring. -/
lemma asIdeal_mem_minimalPrimes_of_isMin {p : PrimeSpectrum A} (hp : IsMin p) :
    p.asIdeal ∈ minimalPrimes A :=
  ⟨⟨p.isPrime, bot_le⟩, fun q hq hle ↦ hp (show (⟨q, hq.1⟩ : PrimeSpectrum A) ≤ p from hle)⟩

/-- Let `A` be a noetherian ring of Krull dimension at most one, `Z = V(I)` a closed subset of
`Spec A` and `x` a point. Then there is a basic open neighbourhood `D(g)` of `x` whose
intersection with the complement of `Z` is again a basic open, `D(g f)`. -/
theorem exists_basicOpen_inter_compl_zeroLocus_eq [IsNoetherianRing A]
    (hA : ringKrullDim A ≤ 1) (I : Ideal A) (x : PrimeSpectrum A) :
    ∃ g f : A, x ∈ basicOpen g ∧
      (basicOpen g : Set (PrimeSpectrum A)) ∩ (zeroLocus (I : Set A))ᶜ = basicOpen (g * f) := by
  classical
  by_cases hx : I ≤ x.asIdeal
  swap
  · obtain ⟨g, hgI, hgx⟩ := Set.not_subset.1 hx
    refine ⟨g, 1, hgx, ?_⟩
    rw [mul_one, Set.inter_eq_left]
    intro y hy hyZ
    exact hy (hyZ hgI)
  -- the minimal primes not containing `I`
  let S : Set (PrimeSpectrum A) := {p | IsMin p ∧ ¬ I ≤ p.asIdeal}
  have hS : S.Finite := by
    refine ((minimalPrimes.finite_of_isNoetherianRing A).preimage
      (fun p _ q _ h ↦ PrimeSpectrum.ext h)).subset fun p hp ↦ ?_
    exact asIdeal_mem_minimalPrimes_of_isMin hp.1
  -- prime avoidance: an element `f ∈ I` outside all of them
  obtain ⟨f, hfI, hfS⟩ : ∃ f ∈ I, ∀ p ∈ S, f ∉ p.asIdeal := by
    by_contra! h
    have hsub : (I : Set A) ⊆ ⋃ p ∈ (↑hS.toFinset : Set (PrimeSpectrum A)), p.asIdeal := by
      intro a ha
      obtain ⟨p, hp, hap⟩ := h a ha
      exact Set.mem_biUnion (by simpa using hp) hap
    obtain ⟨p, hp, hIp⟩ := (Ideal.subset_union_prime x x (fun p _ _ _ ↦ p.isPrime)).1 hsub
    exact ((Set.Finite.mem_toFinset hS).1 hp).2 hIp
  -- a minimal prime containing `f` contains `I`
  have hmin (p : PrimeSpectrum A) (hp : IsMin p) (hfp : f ∈ p.asIdeal) : I ≤ p.asIdeal := by
    by_contra h
    exact hfS p ⟨hp, h⟩ hfp
  -- the points of `V(f)` outside `Z` are minimal over `(f)`, hence finitely many
  let T : Set (PrimeSpectrum A) := {P | f ∈ P.asIdeal ∧ ¬ I ≤ P.asIdeal}
  have hTmin (P : PrimeSpectrum A) (hP : P ∈ T) : ¬ IsMin P := fun h ↦ hP.2 (hmin P h hP.1)
  have hT : T.Finite := by
    refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {f})).preimage
      (fun p _ q _ h ↦ PrimeSpectrum.ext h)).subset fun P hP ↦ ?_
    refine ⟨⟨P.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hP.1⟩, fun Q hQ hQP ↦ ?_⟩
    let Q' : PrimeSpectrum A := ⟨Q, hQ.1⟩
    have hfQ : f ∈ Q := (Ideal.span_singleton_le_iff_mem _).1 hQ.2
    by_contra hPQ
    have hlt : Q' < P := lt_of_le_not_ge hQP hPQ
    exact hP.2 ((hmin Q' (isMin_of_lt_of_ringKrullDim_le_one hA hlt) hfQ).trans hQP)
  -- no point of `T` is contained in `x`
  have hTx (P : PrimeSpectrum A) (hP : P ∈ T) : ∃ h ∈ P.asIdeal, h ∉ x.asIdeal := by
    by_contra! h
    have hle : P ≤ x := h
    have hlt : P < x := lt_of_le_of_ne hle fun e ↦ hP.2 (e ▸ hx)
    exact hTmin P hP (isMin_of_lt_of_ringKrullDim_le_one hA hlt)
  choose! hfun hfunP hfunx using hTx
  refine ⟨∏ P ∈ hT.toFinset, hfun P, f, ?_, ?_⟩
  · change _ ∉ x.asIdeal
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨P, hP, h⟩
    exact hfunx P ((Set.Finite.mem_toFinset hT).1 hP) h
  · ext y
    simp only [Set.mem_inter_iff, SetLike.mem_coe, mem_basicOpen, Set.mem_compl_iff,
      mem_zeroLocus, SetLike.coe_subset_coe]
    constructor
    · rintro ⟨hg, hyI⟩
      refine fun hmem ↦ ?_
      rcases y.isPrime.mem_or_mem hmem with h | h
      · exact hg h
      · have hyT : y ∈ T := ⟨h, hyI⟩
        exact hg (Ideal.IsPrime.prod_mem_iff.mpr ⟨y, by simpa using hyT, hfunP y hyT⟩)
    · intro h
      refine ⟨fun hg ↦ h (Ideal.mul_mem_right _ _ hg), fun hyI ↦ h ?_⟩
      exact Ideal.mul_mem_left _ _ (hyI hfI)

end PrimeSpectrum

namespace AlgebraicGeometry.Scheme

open TopologicalSpace

/-- Let `W` be a locally noetherian scheme of dimension at most one and `O` an open subset. Every
point of `W` has an affine open neighbourhood `V` such that `V ∩ O` is again affine. -/
theorem exists_isAffineOpen_inf_isAffineOpen {W : Scheme.{u}} [IsLocallyNoetherian W]
    (hW : topologicalKrullDim W ≤ 1) (O : W.Opens) (w : W) :
    ∃ V : W.Opens, IsAffineOpen V ∧ w ∈ V ∧ IsAffineOpen (V ⊓ O) := by
  obtain ⟨V₀, hV₀, hwV₀, -⟩ : ∃ V₀ : W.Opens, V₀ ∈ W.affineOpens ∧ w ∈ V₀ ∧ V₀ ≤ ⊤ :=
    (Opens.isBasis_iff_nbhd.1 W.isBasis_affineOpens) (Opens.mem_top w)
  have := IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩
  have hR : ringKrullDim Γ(W, V₀) ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (hV₀.fromSpec.topologicalKrullDim_le_of_etale).trans hW
  obtain ⟨x, rfl⟩ : w ∈ Set.range hV₀.fromSpec := by rwa [hV₀.range_fromSpec]
  let O' : Set (PrimeSpectrum Γ(W, V₀)) := hV₀.fromSpec ⁻¹' (O : Set W)
  have hO' : IsClosed O'ᶜ := (O.isOpen.preimage hV₀.fromSpec.continuous).isClosed_compl
  obtain ⟨g, f, hxg, hgf⟩ := PrimeSpectrum.exists_basicOpen_inter_compl_zeroLocus_eq hR
    (PrimeSpectrum.vanishingIdeal O'ᶜ) x
  rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hO'.closure_eq, compl_compl] at hgf
  refine ⟨W.basicOpen g, hV₀.basicOpen g, ?_, ?_⟩
  · change x ∈ hV₀.fromSpec ⁻¹ᵁ W.basicOpen g
    rwa [hV₀.fromSpec_preimage_basicOpen]
  · convert hV₀.basicOpen (g * f) using 1
    ext y
    constructor
    · rintro ⟨hy, hyO⟩
      obtain ⟨z, rfl⟩ : y ∈ Set.range hV₀.fromSpec := by
        rw [hV₀.range_fromSpec]
        exact W.basicOpen_le g hy
      change z ∈ hV₀.fromSpec ⁻¹ᵁ W.basicOpen g at hy
      rw [hV₀.fromSpec_preimage_basicOpen] at hy
      have : z ∈ (↑(PrimeSpectrum.basicOpen (g * f)) : Set (PrimeSpectrum Γ(W, V₀))) := by
        rw [← hgf]
        exact ⟨hy, hyO⟩
      change z ∈ hV₀.fromSpec ⁻¹ᵁ W.basicOpen (g * f)
      rw [hV₀.fromSpec_preimage_basicOpen]
      exact this
    · intro hy
      obtain ⟨z, rfl⟩ : y ∈ Set.range hV₀.fromSpec := by
        rw [hV₀.range_fromSpec]
        exact W.basicOpen_le _ hy
      change z ∈ hV₀.fromSpec ⁻¹ᵁ W.basicOpen (g * f) at hy
      rw [hV₀.fromSpec_preimage_basicOpen] at hy
      have : z ∈ (↑(PrimeSpectrum.basicOpen g) : Set (PrimeSpectrum Γ(W, V₀))) ∩ O' := by
        rw [hgf]
        exact hy
      refine ⟨?_, this.2⟩
      change z ∈ hV₀.fromSpec ⁻¹ᵁ W.basicOpen g
      rw [hV₀.fromSpec_preimage_basicOpen]
      exact this.1

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- For an open immersion `j : U ⟶ T`, a morphism `w : W ⟶ T` and an open `V'` of `W` such that
`V' ∩ w⁻¹(U)` is affine, the fibre product `V' ×_T U` is affine. -/
lemma isAffine_pullback_of_isAffineOpen_inf {T U W : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (w : W ⟶ T) (V' : W.Opens) (h : IsAffineOpen (V' ⊓ w ⁻¹ᵁ j.opensRange)) :
    IsAffine (pullback (V'.ι ≫ w) j) := by
  have e : Set.range (pullback.fst (V'.ι ≫ w) j ≫ V'.ι) =
      Set.range (V' ⊓ w ⁻¹ᵁ j.opensRange).ι := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, Scheme.Pullback.range_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.preimage_comp, Set.image_preimage_eq_inter_range,
      Scheme.Opens.range_ι]
    ext x
    simp [and_comm]
  have : IsAffine (V' ⊓ w ⁻¹ᵁ j.opensRange).toScheme := h
  exact IsAffine.of_isIso (IsOpenImmersion.isoOfRangeEq _ _ e).hom

end AlgebraicGeometry
