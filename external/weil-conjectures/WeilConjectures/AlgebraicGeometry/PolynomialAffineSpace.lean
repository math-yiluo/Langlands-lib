/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.AffinePresentation

/-!
# Affine spaces over a field as spectra of polynomial rings

For a field `k`, `AlgebraicGeometry.polyAffine k N = Spec k[X₀, …, X_{N-1}]` is the affine space
`𝔸ᴺ_k` as a scheme over `Spec k`, with the projection `AlgebraicGeometry.polyAffineProj` forgetting
the first coordinate, which is smooth of relative dimension one. Every affine scheme of finite type
over `k` is a closed subscheme of some `𝔸ᴺ_k`
(`AlgebraicGeometry.exists_isClosedImmersion_polyAffine`), and `𝔸⁰_k = Spec k`.

## Implementation notes

The underlying scheme of `polyAffine k N` is isomorphic to `Mathlib`'s `𝔸(Fin N; Spec k)`
(`AlgebraicGeometry.AffineSpace.SpecIso`), which is defined as a base change of `𝔸(Fin N; Spec ℤ)`.
The spectrum of the polynomial ring is used here because the arguments are ring-theoretic
(presentations of finitely generated `k`-algebras, the morphism `MvPolynomial.rename Fin.succ`), and
morphisms out of it are `Spec.map` of ring homomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The affine space `𝔸ᴺ_k = Spec k[X₀, …, X_{N-1}]`, as a scheme over `Spec k`. -/
noncomputable def polyAffine (N : ℕ) : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin N) k))))

instance (N : ℕ) : LocallyOfFiniteType (polyAffine k N).hom := by
  dsimp [polyAffine]
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom]
  exact RingHom.finiteType_algebraMap.2 inferInstance

instance (N : ℕ) : QuasiCompact (polyAffine k N).hom := by
  dsimp [polyAffine]; infer_instance

instance (N : ℕ) : IsSeparated (polyAffine k N).hom := by
  dsimp [polyAffine]; infer_instance

instance : IsIso (polyAffine k 0).hom := by
  dsimp only [polyAffine, Over.mk_hom]
  let e : CommRingCat.of k ≅ CommRingCat.of (MvPolynomial (Fin 0) k) :=
    (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.toRingEquiv.toCommRingCatIso
  have he : e.hom = CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 0) k)) := by
    apply CommRingCat.hom_ext; apply RingHom.ext; intro r
    change (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm r = _
    exact (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.commutes r
  rw [← he]
  infer_instance

/-- The ring map `k[X₀, …, X_{N-1}] ⟶ k[X₀, …, X_N]`, `Xᵢ ↦ X_{i+1}`. -/
noncomputable def polyAffineProjRingHom (N : ℕ) :
    MvPolynomial (Fin N) k →+* MvPolynomial (Fin (N + 1)) k :=
  (MvPolynomial.rename Fin.succ).toRingHom

lemma polyAffineProjRingHom_eq (N : ℕ) :
    polyAffineProjRingHom k N =
      (MvPolynomial.finSuccEquiv k N).symm.toRingEquiv.toRingHom.comp Polynomial.C := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · change MvPolynomial.rename Fin.succ (MvPolynomial.C r) =
      (MvPolynomial.finSuccEquiv k N).symm (Polynomial.C (MvPolynomial.C r))
    rw [eq_comm, AlgEquiv.symm_apply_eq, MvPolynomial.rename_C]
    exact ((MvPolynomial.finSuccEquiv k N).commutes r).symm
  · simp only [polyAffineProjRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.rename_X, RingHom.coe_comp, Function.comp_apply]
    rw [eq_comm, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.symm_apply_eq, MvPolynomial.finSuccEquiv_X_succ]

lemma isStandardSmoothOfRelativeDimension_polynomial (R : Type u) [CommRing R] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (Polynomial R) := by
  have := isStandardSmoothOfRelativeDimension_mvPolynomial R 1
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
    (MvPolynomial.uniqueAlgEquiv R (Fin 1))

lemma isStandardSmoothOfRelativeDimension_polyAffineProjRingHom (N : ℕ) :
    (polyAffineProjRingHom k N).IsStandardSmoothOfRelativeDimension 1 := by
  rw [polyAffineProjRingHom_eq]
  refine RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 Polynomial.C
    (MvPolynomial.finSuccEquiv k N).symm.toRingEquiv ?_
  rw [← Polynomial.algebraMap_eq]
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).2
    (isStandardSmoothOfRelativeDimension_polynomial _)

/-- The projection `𝔸^{N+1}_k ⟶ 𝔸^N_k` forgetting the first coordinate. -/
noncomputable def polyAffineProj (N : ℕ) : polyAffine k (N + 1) ⟶ polyAffine k N :=
  Over.homMk (Spec.map (CommRingCat.ofHom (polyAffineProjRingHom k N))) (by
    dsimp [polyAffine]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [polyAffineProjRingHom, ← MvPolynomial.algebraMap_eq])

instance (N : ℕ) : SmoothOfRelativeDimension 1 (polyAffineProj k N).left := by
  change SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (polyAffineProjRingHom k N)))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1), CommRingCat.hom_ofHom]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    (isStandardSmoothOfRelativeDimension_polyAffineProjRingHom k N)

variable {k} in
/-- An affine scheme of finite type over `k` is a closed subscheme of some `𝔸ᴺ_k`. -/
theorem exists_isClosedImmersion_polyAffine (V : Over (Spec (.of k))) [IsAffine V.left]
    [LocallyOfFiniteType V.hom] :
    ∃ (N : ℕ) (ι : V ⟶ polyAffine k N), IsClosedImmersion ι.left := by
  let φ : k →+* Γ(V.left, ⊤) := V.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hft : V.hom.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop @LocallyOfFiniteType V.hom ‹_›
  have hφ : φ.FiniteType := hft.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  let := φ.toAlgebra
  have : Algebra.FiniteType k Γ(V.left, ⊤) := hφ
  obtain ⟨N, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  refine ⟨N, Over.homMk (V.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)) ?_, ?_⟩
  · change (V.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin N) k))) = V.hom
    have h : ψ.toRingHom.comp (algebraMap k (MvPolynomial (Fin N) k)) = φ := by
      ext r; exact ψ.commutes r
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom, Spec.map_comp,
      ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Scheme.isoSpec_Spec_hom,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  · have : IsClosedImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
      .spec_of_surjective _ hψ
    exact inferInstanceAs (IsClosedImmersion
      (V.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)))

end AlgebraicGeometry
