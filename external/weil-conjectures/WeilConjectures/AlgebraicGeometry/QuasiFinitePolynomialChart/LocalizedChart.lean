/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Geometric realization of a localized polynomial map

## References

* Stacks Project, Tag 00QE, as used at the start of the proof of Tag 00RH
* Stacks Project, Tag 00QE, the first reduction in the proof of Tag 00RH, and Tag 00E4
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem quasiFinite_of_primewise
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (hq : ∀ q : PrimeSpectrum B, Algebra.IsQuasiFiniteAtPrime A B q) :
    Algebra.QuasiFinite A B := by
  apply Algebra.QuasiFinite.iff_finite_comap_preimage_singleton.mpr
  intro p
  let E := PrimeSpectrum.preimageHomeomorphFiber A B p
  have : DiscreteTopology (PrimeSpectrum (p.asIdeal.Fiber B)) :=
    discreteTopology_iff_isOpen_singleton.mpr fun Q ↦ by
      obtain ⟨⟨q, hp⟩, rfl⟩ := E.surjective Q
      have hp' : q.comap (algebraMap A B) = p := hp
      subst p
      exact hq q
  have : Finite (PrimeSpectrum (p.asIdeal.Fiber B)) := finite_of_compact_of_discrete
  have : Finite (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}) :=
    E.toEquiv.finite_iff.mpr inferInstance
  exact Set.toFinite _

/-- A supplied quasi-finite polynomial map to a localization gives a chart on that basic open.
-/
theorem exists_chart_of_localized_polynomial_map
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [LocallyOfFinitePresentation f]
    [Algebra Γ(T, ⊤) Γ(X, ⊤)]
    (halg : algebraMap Γ(T, ⊤) Γ(X, ⊤) = f.appTop.hom)
    (g : Γ(X, ⊤)) (n : ℕ)
    (φ : MvPolynomial (Fin n) Γ(T, ⊤) →ₐ[Γ(T, ⊤)] Localization.Away g)
    (hft : @Algebra.FiniteType (MvPolynomial (Fin n) Γ(T, ⊤)) (Localization.Away g)
      _ _ φ.toRingHom.toAlgebra)
    (hq : ∀ q : PrimeSpectrum (Localization.Away g),
      @Algebra.IsQuasiFiniteAtPrime (MvPolynomial (Fin n) Γ(T, ⊤)) (Localization.Away g)
        _ _ φ.toRingHom.toAlgebra hft q) :
    ∃ e : (X.basicOpen g).toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T,
      LocallyOfFinitePresentation e ∧ LocallyQuasiFinite e ∧
      e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = (X.basicOpen g).ι ≫ f := by
  let A := Γ(T, ⊤)
  let B := Γ(X, ⊤)
  let P := MvPolynomial (Fin n) A
  let L := Localization.Away g
  let : Algebra P L := φ.toRingHom.toAlgebra
  let : Algebra.FiniteType P L := hft
  have hqf : φ.toRingHom.QuasiFinite := quasiFinite_of_primewise hq
  have hfp : φ.toRingHom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_comp_finiteType (algebraMap A P)
    · have hφ : φ.toRingHom.comp (algebraMap A P) = algebraMap A L := φ.comp_algebraMap
      rw [hφ, IsScalarTower.algebraMap_eq A B L, halg]
      exact RingHom.FinitePresentation.comp
        (RingHom.finitePresentation_algebraMap.mpr inferInstance) f.finitePresentation_appTop
    · exact RingHom.finiteType_algebraMap.mpr inferInstance
  let U := X.basicOpen g
  let hU : IsAffineOpen U := (isAffineOpen_top X).basicOpen g
  let E := IsLocalization.algEquiv (Submonoid.powers g) L Γ(X, U)
  let V := ULift.{u} (Fin n)
  let ρ := MvPolynomial.renameEquiv A (Equiv.ulift : V ≃ Fin n)
  let ψ := E.toRingHom.comp (φ.toRingHom.comp ρ.toRingHom)
  let e : U.toScheme ⟶ AffineSpace V T :=
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ) ≫ (AffineSpace.isoOfIsAffine V T).inv
  refine ⟨e, ?_, ?_, ?_⟩
  · have hψ : ψ.FinitePresentation :=
      (RingHom.FinitePresentation.of_bijective E.bijective).comp
        (hfp.comp (RingHom.FinitePresentation.of_bijective ρ.bijective))
    have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom ψ)) :=
      (LocallyOfFinitePresentation.SpecMap_iff _).mpr hψ
    dsimp [e]
    infer_instance
  · have hψ : ψ.QuasiFinite :=
      (RingHom.QuasiFinite.of_finite E.toRingEquiv.finite).comp
        (hqf.comp (RingHom.QuasiFinite.of_finite ρ.toRingEquiv.finite))
    have : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom ψ)) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mpr hψ
    dsimp [e]
    infer_instance
  · dsimp [e]
    rw [Category.assoc, Category.assoc, AffineSpace.isoOfIsAffine_inv_over,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    have hψ : ψ.comp MvPolynomial.C =
        (algebraMap B Γ(X, U)).comp f.appTop.hom := by
      ext a
      change E (φ (ρ (algebraMap A (MvPolynomial V A) a))) = _
      rw [ρ.commutes, φ.commutes, IsScalarTower.algebraMap_apply A B L, E.commutes, halg]
      rfl
    rw [hψ, CommRingCat.ofHom_comp, Spec.map_comp]
    simp only [Category.assoc, CommRingCat.ofHom_hom]
    rw [Scheme.isoSpec_inv_naturality]
    rw [← Category.assoc]
    suffices hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, U))) ≫
        X.isoSpec.inv = U.ι by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ f) this
    rw [← Category.assoc, Iso.comp_inv_eq]
    rw [← hU.isoSpec_hom_fromSpec_assoc]
    change hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, U))) =
      hU.isoSpec.hom ≫ hU.fromSpec ≫ X.toSpecΓ
    rw [hU.fromSpec_toSpecΓ]
    rfl

end AlgebraicGeometry
