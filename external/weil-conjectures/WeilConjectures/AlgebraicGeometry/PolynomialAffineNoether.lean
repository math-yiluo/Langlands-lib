/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.PolynomialAffineHyperplane
public import WeilConjectures.RingTheory.NagataCoordinateChange

/-!
# Noether normalisation of a closed subset of the coordinate hyperplane

Let `Y` be a closed subset of `𝔸^{N+2}_k = Spec k[X₀, …, X_{N+1}]` contained in, but not equal to,
the coordinate hyperplane `V(X_{N+1})`. After an automorphism `ψ` of `𝔸^{N+2}_k` preserving the
hyperplane, the projection `𝔸^{N+2}_k ⟶ 𝔸^{N+1}_k` forgetting `X₀` is finite on `Y`
(`AlgebraicGeometry.exists_isFinite_polyAffineProj`). This is the Noether normalisation step in the
proof of blueprint `theorem-verdier-s-theorem-specialization-zero`. The blueprint uses a linear
change of coordinates, which needs an infinite field; Nagata's change of coordinates
`Xᵢ ↦ Xᵢ + X₀^{rᵢ}` works over every field.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

variable (k) in
/-- The points of the coordinate hyperplane `V(X_N) ⊆ 𝔸^{N+1}_k` are the primes containing
`X_N`. -/
lemma coe_support_polyAffineHyperplane (N : ℕ) :
    ((polyAffineHyperplane k N).support : Set (polyAffine k (N + 1)).left) =
      PrimeSpectrum.zeroLocus {MvPolynomial.X (Fin.last N)} := by
  rw [polyAffineHyperplane, Scheme.IdealSheafData.coe_support_ofIdealTop, Scheme.zeroLocus_span]
  refine (Spec_zeroLocus _).trans ?_
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, polyAffineCoord]
  exact (ConcreteCategory.bijective_of_isIso _).1.eq_iff

/-- The automorphism of `𝔸ᴺ_k` induced by a `k`-algebra automorphism `σ` of `k[X₀, …, X_{N-1}]`;
its underlying morphism of schemes is `Spec σ`. -/
noncomputable def polyAffineIsoOfAlgEquiv {N : ℕ}
    (σ : MvPolynomial (Fin N) k ≃ₐ[k] MvPolynomial (Fin N) k) :
    polyAffine k N ≅ polyAffine k N :=
  Over.isoMk
    (show Spec (.of (MvPolynomial (Fin N) k)) ≅ Spec (.of (MvPolynomial (Fin N) k)) from
      { hom := Spec.map (CommRingCat.ofHom σ.toRingHom)
        inv := Spec.map (CommRingCat.ofHom σ.symm.toRingHom)
        hom_inv_id := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
          congr 1
          exact CommRingCat.hom_ext (RingHom.ext fun x ↦ by simp)
        inv_hom_id := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
          congr 1
          exact CommRingCat.hom_ext (RingHom.ext fun x ↦ by simp) })
    (by
      dsimp [polyAffine]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext σ.commutes)

lemma polyAffineIsoOfAlgEquiv_hom_left {N : ℕ}
    (σ : MvPolynomial (Fin N) k ≃ₐ[k] MvPolynomial (Fin N) k) :
    (polyAffineIsoOfAlgEquiv σ).hom.left = Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  rfl

/-- **Noether normalisation on the coordinate hyperplane**: for a closed subset `Y` of
`𝔸^{N+2}_k` contained in, but not equal to, the coordinate hyperplane `V(X_{N+1})`, there are an
automorphism `ψ` of `𝔸^{N+2}_k` preserving `V(X_{N+1})` schematically and a morphism
`a : V ⟶ 𝔸^{N+2}_k` whose image contains `Y`, such that `V ⟶ 𝔸^{N+2}_k ⟶ 𝔸^{N+2}_k ⟶ 𝔸^{N+1}_k`
(the last map forgetting `X₀`) is finite. -/
theorem exists_isFinite_polyAffineProj (N : ℕ) {Y : Set (polyAffine k (N + 2)).left}
    (hY : IsClosed Y)
    (hYH : Y ⊆ ((polyAffineHyperplane k (N + 1)).support : Set (polyAffine k (N + 2)).left))
    (hne : ¬ ((polyAffineHyperplane k (N + 1)).support : Set (polyAffine k (N + 2)).left) ⊆ Y) :
    ∃ (ψ : polyAffine k (N + 2) ≅ polyAffine k (N + 2)) (V : Scheme.{u})
      (a : V ⟶ (polyAffine k (N + 2)).left),
      Y ⊆ Set.range a.base ∧ IsFinite (a ≫ ψ.hom.left ≫ (polyAffineProj k (N + 1)).left) ∧
      (polyAffineHyperplane k (N + 1)).comap ψ.hom.left = polyAffineHyperplane k (N + 1) := by
  rw [coe_support_polyAffineHyperplane] at hYH hne
  obtain ⟨g, hg0, hg⟩ := MvPolynomial.exists_rename_castSucc_mem_vanishingIdeal hY hYH hne
  obtain ⟨σ, hσX, hσ⟩ :=
    NoetherNormalization.exists_algEquiv_isUnit_leadingCoeff_rename_castSucc g hg0
  set g' := MvPolynomial.rename Fin.castSucc g
  refine ⟨polyAffineIsoOfAlgEquiv σ.symm, Spec (.of (MvPolynomial (Fin (N + 2)) k ⧸
    Ideal.span {g'})), Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)), fun x hx ↦ ?_, ?_, ?_⟩
  · have hx' : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {g'}))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        PrimeSpectrum.zeroLocus_span, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hg x hx
    exact hx'
  · have hq : (polyAffineProj k (N + 1)).left =
        Spec.map (CommRingCat.ofHom (polyAffineProjRingHom k (N + 1))) := rfl
    rw [polyAffineIsoOfAlgEquiv_hom_left, hq, ← Spec.map_comp, ← Spec.map_comp,
      IsFinite.SpecMap_iff, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      CommRingCat.hom_ofHom]
    have hle : Ideal.span {σ g'} ≤ (Ideal.span {g'}).comap σ.symm.toRingHom := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      simp
    exact (RingHom.Finite.of_surjective _
      (Ideal.quotientMap_surjective (H := hle) σ.symm.surjective)).comp
      (MvPolynomial.finite_quotient_comp_rename_succ _ hσ)
  · rw [polyAffineHyperplane, Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span,
      Set.image_singleton]
    congr 3
    rw [polyAffineCoord, polyAffineIsoOfAlgEquiv_hom_left]
    refine (Scheme.specMap_appTop_ΓSpecIso_inv _ _).trans ?_
    simp [σ.symm_apply_eq.mpr hσX.symm]

end AlgebraicGeometry
