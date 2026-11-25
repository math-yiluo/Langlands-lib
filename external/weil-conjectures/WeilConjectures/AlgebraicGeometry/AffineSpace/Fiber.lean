/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Polynomial

/-!
# Generic behaviour of an open subset of the affine line

Let `V` be an integral affine scheme and `U` a nonempty open subset of the affine line `𝔸¹_V`.
Then over a nonempty basic open `D(b)` of `V`, every fibre of `𝔸¹_V ⟶ V` meets `U`, and the
complement of `U` has finite fibres
(`AlgebraicGeometry.AffineSpace.exists_basicOpen_forall_exists_mem_and_finite`): the complement
of `U` is contained in the zero locus of a nonzero polynomial `g`, and one takes for `b` the
leading coefficient of `g`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AffineSpace

/-- Let `U` be a nonempty open subset of the affine line `𝔸¹_V` over an integral affine scheme `V`.
There is a nonempty basic open `D(b)` of `V` over which every fibre of `𝔸¹_V ⟶ V` meets `U` and
the complement of `U` has finite fibres. -/
theorem exists_basicOpen_forall_exists_mem_and_finite {V : Scheme.{u}} [IsAffine V]
    [IsIntegral V] (U : 𝔸(PUnit.{u + 1}; V).Opens)
    (hU : (U : Set 𝔸(PUnit.{u + 1}; V)).Nonempty) :
    ∃ b : Γ(V, ⊤), (V.basicOpen b : Set V).Nonempty ∧ ∀ s ∈ V.basicOpen b,
      (∃ x ∈ U, (𝔸(PUnit.{u + 1}; V) ↘ V) x = s) ∧
        {x | x ∉ U ∧ (𝔸(PUnit.{u + 1}; V) ↘ V) x = s}.Finite := by
  set R := Γ(V, ⊤)
  set φ := isoOfIsAffine PUnit.{u + 1} V
  set e : MvPolynomial PUnit.{u + 1} R ≃ₐ[R] Polynomial R := MvPolynomial.uniqueAlgEquiv (R := R) _
  -- the points of `𝔸¹_V` are the primes of `R[X]`
  set Ψ := (Scheme.homeoOfIso φ).trans (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv)
  have hC : (e.symm.toRingEquiv : Polynomial R →+* MvPolynomial PUnit.{u + 1} R).comp
      Polynomial.C = MvPolynomial.C := by
    refine RingHom.ext fun r ↦ ?_
    exact e.symm.commutes r
  have hΨ (x : 𝔸(PUnit.{u + 1}; V)) :
      PrimeSpectrum.comap Polynomial.C (Ψ x) = V.isoSpec.hom ((𝔸(PUnit.{u + 1}; V) ↘ V) x) := by
    have h1 : φ.hom ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
        (𝔸(PUnit.{u + 1}; V) ↘ V) ≫ V.isoSpec.hom := by
      rw [← cancel_epi φ.inv, Iso.inv_hom_id_assoc, isoOfIsAffine_inv_over_assoc,
        Iso.inv_hom_id, Category.comp_id]
    have h2 := congrArg (fun f ↦ f x) h1
    simp only [Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom] at h2
    refine Eq.trans ?_ h2
    rw [← hC, PrimeSpectrum.comap_comp_apply]
    rfl
  -- the complement of `U`, as a closed proper subset of `Spec R[X]`
  set Z := Ψ '' (U : Set 𝔸(PUnit.{u + 1}; V))ᶜ
  have hZ : IsClosed Z := Ψ.isClosedMap _ U.isOpen.isClosed_compl
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨g, hgZ, hgx₀⟩ : ∃ g ∈ PrimeSpectrum.vanishingIdeal Z, g ∉ (Ψ x₀).asIdeal := by
    by_contra! h
    have : Ψ x₀ ∈ Z := by
      rw [← hZ.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact h
    obtain ⟨y, hy, hyx⟩ := this
    exact hy (Ψ.injective hyx ▸ hx₀)
  have hg0 : g ≠ 0 := fun h ↦ hgx₀ (h ▸ (Ψ x₀).asIdeal.zero_mem)
  have hgZ' (x : 𝔸(PUnit.{u + 1}; V)) (hx : x ∉ U) : g ∈ (Ψ x).asIdeal :=
    (PrimeSpectrum.mem_vanishingIdeal _ _).1 hgZ _ ⟨x, hx, rfl⟩
  refine ⟨g.leadingCoeff, ?_, fun s hs ↦ ?_⟩
  · by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : V.basicOpen g.leadingCoeff = ⊥ := SetLike.coe_injective (by simpa using h)
    exact hg0 (Polynomial.leadingCoeff_eq_zero.1 ((basicOpen_eq_bot_iff _).1 this))
  have hbs : g.leadingCoeff ∉ (V.isoSpec.hom s).asIdeal := by
    rw [← V.toSpecΓ_preimage_basicOpen] at hs
    exact hs
  refine ⟨?_, ?_⟩
  · obtain ⟨Q, hgQ, hQ⟩ := Polynomial.exists_primeSpectrum_notMem_comap_C_eq _ hbs
    refine ⟨Ψ.symm Q, by_contra fun hx ↦ hgQ ?_, V.isoSpec.hom.homeomorph.injective ?_⟩
    · simpa using hgZ' _ hx
    · rw [Scheme.Hom.homeomorph_apply, Scheme.Hom.homeomorph_apply, ← hΨ,
        Homeomorph.apply_symm_apply, hQ]
  · refine ((Polynomial.finite_setOf_mem_comap_C_eq _ hbs).preimage Ψ.injective.injOn).subset
      fun x ⟨hxU, hxs⟩ ↦ ⟨hgZ' x hxU, ?_⟩
    rw [hΨ, hxs]

/-- The image of the base change `𝔸ⁿ_S ⟶ 𝔸ⁿ_T` of a morphism `f : S ⟶ T` is the preimage of the
image of `f`. -/
lemma range_map {n : Type u} {S T : Scheme.{u}} (f : S ⟶ T) :
    Set.range (map n f) = (𝔸(n; T) ↘ T) ⁻¹' Set.range f := by
  have h := isPullback_map (n := n) f
  have hs : Set.range h.isoPullback.hom = Set.univ := by
    rw [← Scheme.coe_homeoOfIso]
    exact (Scheme.homeoOfIso _).range_coe
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hs,
    Set.image_univ, Scheme.Pullback.range_fst]

end AlgebraicGeometry.AffineSpace
