/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict

/-! # Openness of the image of a quotient factor over an isomorphism locus

Source: Stacks Project, More on Algebra, proof of Tag 09XH.
(blueprint: lem-weil-pbc-quotient-first-factor-image-open)
-/

@[expose] public section

universe u w z

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

/-- The first product factor has spectrum image the basic open of its idempotent.

Source: Stacks Project, proof of Tag 09XH, first-factor spectrum identification.
Auxiliary calculation for (blueprint: lem-weil-pbc-quotient-first-factor-image-open).
The kernel of the first projection consists of the complementary factor. A prime
contains it exactly when it omits the first-factor idempotent: use their sum 1
in one direction and their product 0 in the other. -/
theorem firstFactor_range
    {R : Type u} {D₁ : Type w} {D₂ : Type z}
    [CommRing R] [CommRing D₁] [CommRing D₂] (e : R ≃+* D₁ × D₂) :
    Set.range (PrimeSpectrum.comap ((RingHom.fst D₁ D₂).comp e.toRingHom)) =
      (PrimeSpectrum.basicOpen (e.symm (1, 0)) : Set _) := by
  let k := (RingHom.fst D₁ D₂).comp e.toRingHom
  have hk : Function.Surjective k := Prod.fst_surjective.comp e.surjective
  rw [range_comap_of_surjective D₁ k hk]
  ext p
  change ((RingHom.ker k : Set R) ⊆ (p.asIdeal : Set R)) ↔ e.symm (1, 0) ∉ p.asIdeal
  constructor
  · intro h he
    have hmem : 1 - e.symm (1, 0) ∈ RingHom.ker k := by
      simp [k]
    have hone := p.asIdeal.add_mem he (h hmem)
    simp only [add_sub_cancel] at hone
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p.asIdeal hone isUnit_one)
  · intro he a ha
    have hm : a * e.symm (1, 0) = 0 := by
      apply e.injective
      have ha' : (e a).1 = 0 := ha
      ext <;> simp [ha']
    exact (p.isPrime.mem_or_mem (hm ▸ p.asIdeal.zero_mem)).resolve_right he

/-- A component of a closed fibre has relatively open image over an isomorphism locus.

Source: literature/stacks-project/more-algebra.tex:2529-2541, proof of Tag 09XH.
(blueprint: lem-weil-pbc-quotient-first-factor-image-open).

Choose a lift t of e.symm (1,0). The first factor spectrum is V(J) intersect D(t):
a prime containing J contains exactly one of t and 1-t, since their product lies in J.
The equality J = map i J' identifies V(J) with the inverse image of V(J').
On the inverse image of U, the scheme isomorphism induces a homeomorphism to U.
It sends the open intersection with D(t) to an open W in Spec(S'). The image of
our factor is W intersect V(J'), because every point of the factor lies over U.
Pullback along the quotient spectrum therefore gives an open subset. -/
theorem quotient_firstFactor_image_isOpen
    {S' S : Type u} [CommRing S'] [CommRing S] (i : S' →+* S)
    (J' : Ideal S') (J : Ideal S) (hJ : Ideal.map i J' = J)
    {D₁ : Type w} {D₂ : Type z} [CommRing D₁] [CommRing D₂]
    (e : (S ⧸ J) ≃+* D₁ × D₂) (U : (Spec (.of S')).Opens)
    (hiso : IsIso (Spec.map (CommRingCat.ofHom i) ∣_ U))
    (hT : Set.range (PrimeSpectrum.comap
      ((RingHom.fst D₁ D₂).comp (e.toRingHom.comp (Ideal.Quotient.mk J)))) ⊆
        (PrimeSpectrum.comap i) ⁻¹' U.1) :
    IsOpen ((PrimeSpectrum.comap (Ideal.Quotient.mk J')) ⁻¹'
      ((PrimeSpectrum.comap i) '' Set.range (PrimeSpectrum.comap
        ((RingHom.fst D₁ D₂).comp (e.toRingHom.comp (Ideal.Quotient.mk J)))))) := by
  classical
  let π := Ideal.Quotient.mk J
  let π' := Ideal.Quotient.mk J'
  let φ := PrimeSpectrum.comap i
  let T := Set.range (PrimeSpectrum.comap
    ((RingHom.fst D₁ D₂).comp (e.toRingHom.comp π)))
  let c := e.symm (1, 0)
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective c
  have htimage : T = PrimeSpectrum.comap π '' (PrimeSpectrum.basicOpen c : Set _) := by
    change Set.range (PrimeSpectrum.comap
      (((RingHom.fst D₁ D₂).comp e.toRingHom).comp π)) = _
    rw [PrimeSpectrum.comap_comp, Set.range_comp, firstFactor_range e]
  have hTfibre : T = (PrimeSpectrum.basicOpen t : Set _) ∩ PrimeSpectrum.zeroLocus J := by
    rw [htimage]
    have hc : (PrimeSpectrum.basicOpen c : Set _) =
        (PrimeSpectrum.comap π) ⁻¹' (PrimeSpectrum.basicOpen t : Set _) := by
      rw [← ht]
      rfl
    rw [hc, Set.image_preimage_eq_inter_range,
      range_comap_of_surjective _ π Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  let F := Spec.map (CommRingCat.ofHom i)
  let G := (F ∣_ U) ≫ U.ι
  let V : Set (F ⁻¹ᵁ U).toScheme :=
    {x | (x.1 : PrimeSpectrum S) ∈ PrimeSpectrum.basicOpen t}
  have hV : IsOpen V := (PrimeSpectrum.basicOpen t).isOpen.preimage continuous_subtype_val
  have hWopen : IsOpen (φ '' ((PrimeSpectrum.basicOpen t : Set _) ∩ φ ⁻¹' U.1)) := by
    have hopen := G.isOpenEmbedding.isOpenMap V hV
    have himg : G '' V = φ '' ((PrimeSpectrum.basicOpen t : Set _) ∩ φ ⁻¹' U.1) := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.1, ⟨hx, x.2⟩, by simp [G, F, φ, Spec.map_apply]⟩
      · rintro ⟨x, ⟨hx, hxU⟩, rfl⟩
        exact ⟨⟨x, hxU⟩, hx, by simp [G, F, φ, Spec.map_apply]⟩
    rw [himg] at hopen
    exact hopen
  have hfibre (q : PrimeSpectrum S) :
      φ q ∈ PrimeSpectrum.zeroLocus J' ↔ q ∈ PrimeSpectrum.zeroLocus J := by
    change J' ≤ Ideal.comap i q.asIdeal ↔ J ≤ q.asIdeal
    rw [← Ideal.map_le_iff_le_comap, hJ]
  have himage : φ '' T =
      (φ '' ((PrimeSpectrum.basicOpen t : Set _) ∩ φ ⁻¹' U.1)) ∩
        PrimeSpectrum.zeroLocus J' := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hq' := hq
      rw [hTfibre] at hq'
      exact ⟨⟨q, ⟨hq'.1, hT hq⟩, rfl⟩, (hfibre q).mpr hq'.2⟩
    · rintro ⟨⟨q, ⟨hqt, hqU⟩, rfl⟩, hqJ⟩
      refine ⟨q, ?_, rfl⟩
      rw [hTfibre]
      exact ⟨hqt, (hfibre q).mp hqJ⟩
  have hπfibre : (PrimeSpectrum.comap π') ⁻¹' PrimeSpectrum.zeroLocus J' = Set.univ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    change J' ≤ Ideal.comap π' p.asIdeal
    intro b hb
    change π' b ∈ p.asIdeal
    have hz : π' b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    rw [hz]
    exact p.asIdeal.zero_mem
  change IsOpen ((PrimeSpectrum.comap π') ⁻¹' (φ '' T))
  rw [himage, Set.preimage_inter, hπfibre, Set.inter_univ]
  exact hWopen.preimage (PrimeSpectrum.continuous_comap π')

end AlgebraicGeometry
