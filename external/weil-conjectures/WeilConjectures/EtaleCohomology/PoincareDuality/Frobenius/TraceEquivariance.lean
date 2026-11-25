/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UnitOrientation
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism.Point
public import WeilConjectures.EtaleCohomology.Purity.Smooth.FrobeniusOrientation
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit

/-!
# Weil equivariance of the smooth trace on a geometric fibre

Let `X₀` be a smooth separated scheme of finite type and relative dimension `d` over a finite field
`k₀ = 𝔽_q`, `a : X ⟶ Spec k̄` its geometric fibre and `σ` the geometric Frobenius of `Spec k̄`, so
that the geometric Galois Frobenius `g` of `X` fits in the cartesian square `g ≫ a = a ≫ σ`
(`AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius`). Smooth purity and the smooth
trace are Weil equivariant (blueprint `proposition-purity-trace-commute-frobenius` of the
six-functor section, for the Tate datum of `definition-weil-structure--1`, on which geometric
Frobenius acts by `q⁻ᵈ` on `Λ(d)`). This file records that statement, in the untwisted form in which
the Frobenius files use it
(`AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing_frobeniusOperator`):
there are a Tate orientation `γ` of `a` and a Weil datum `τ` on `Λ_{k̄}(-d)`, on whose sections
Frobenius acts by `q^d`, for which the untwisted smooth trace `(Ra_! Λ_X)[2d] ⟶ Λ_{k̄}(-d)` is a
morphism of Weil objects.

The statement is existential: the orientation is built from an untwisted orientation
`o : Λ_X[2d] ≅ Ra^! Λ` on which geometric Frobenius acts by `q^d`
(`AlgebraicGeometry.Etale.exists_iso_dualizingComplex_isWeilMorphism`, the Frobenius case of the
base change compatibility of purity) and a trivialization of `Λ_{k̄}(d)`
(`AlgebraicGeometry.Etale.TateOrientation.ofUnit`). Its untwisted smooth trace is the unit trace
of `o` followed by an isomorphism `Λ_{k̄} ≅ Λ_{k̄}(-d)`
(`AlgebraicGeometry.Etale.TateOrientation.untwistedSmoothTrace_ofUnit`), and `τ` is `q^d` times
the canonical datum, carried along that isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k₀)) (d : ℕ)
  [SmoothOfRelativeDimension d f] [IsSeparated f] [QuasiCompact f]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
  [HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k₀)))]
  [HasInvertibleExponent Λ f.geometricFiber]
  [HasCompactification f.geometricFiberToAlgebraicClosure]

/-- Blueprint `proposition-purity-trace-commute-frobenius` (Weil equivariance of purity and
trace, with the Tate datum `definition-weil-structure--1`), for the geometric fibre
`a : X ⟶ Spec k̄` of a smooth separated `𝔽_q`-scheme of finite type and relative dimension `d`, in
untwisted form: there are a Tate orientation `γ` of `a` and a Weil datum `τ` on `Λ_{k̄}(-d)` for the
geometric Frobenius of `Spec k̄`, on whose sections Frobenius acts by `q^d`, such that the untwisted
smooth trace of `γ` is a morphism of Weil objects from the datum induced by the canonical datum of
`Λ_X` (through `Ra_!` and the shift by `2d`) to `τ`. -/
theorem exists_tateOrientation_isWeilMorphism_untwistedSmoothTrace :
    ∃ (γ : TateOrientation Λ f.geometricFiberToAlgebraicClosure d)
      (τ : (L(((specGeometricFrobenius k₀).asIso.hom)^*[ModuleCat.{u + 1} Λ])).obj
          (tateObject Λ (Spec (.of (AlgebraicClosure k₀))) (-d)) ⟶
        tateObject Λ (Spec (.of (AlgebraicClosure k₀))) (-d)),
      IsWeilMorphism (specGeometricFrobenius k₀).asIso.hom
          (shiftWeilDatum (specGeometricFrobenius k₀).asIso.hom
            (lowerShriekWeilDatum f.isPullback_geometricGaloisFrobenius
              (leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.asIso.hom).hom) (2 * d))
          τ γ.untwistedSmoothTrace ∧
        ∀ z, frobeniusOperator (specGeometricFrobenius k₀).asIso.hom τ z =
          ((Nat.card k₀ : Λ) ^ d) • z :=
  by
  obtain ⟨o, ho⟩ := exists_iso_dualizingComplex_isWeilMorphism f d Λ
  obtain ⟨e⟩ := nonempty_tateObject_iso_unit Λ (AlgebraicClosure k₀) (d : ℤ)
  have sq := f.isPullback_geometricGaloisFrobenius
  set σ := (specGeometricFrobenius k₀).asIso.hom
  set c : Λ := (Nat.card k₀ : Λ) ^ d
  let E := TateOrientation.unitIsoTateObjectNeg e
  refine ⟨TateOrientation.ofUnit o e, (L((σ)^*[ModuleCat.{u + 1} Λ])).map E.inv ≫
    (c • (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) σ).hom) ≫ E.hom, ?_, fun z ↦ ?_⟩
  · -- The unit trace is a morphism of Weil objects to `q^d` times the canonical datum.
    have h3 : IsWeilMorphism σ (lowerShriekWeilDatum sq
        (c • upperShriekMateWeilDatum (Λ := Λ) sq
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) σ).hom))
        (c • (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) σ).hom)
        ((rightDerivedUpperShriekAdjunction Λ f.geometricFiberToAlgebraicClosure).counit.app
          (𝟙_ _)) := by
      have h := isWeilMorphism_counit_upperShriekMateWeilDatum (Λ := Λ) sq
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) σ).hom
      unfold IsWeilMorphism lowerShriekWeilDatum at h ⊢
      simp only [Functor.map_smul, Linear.comp_smul, Linear.smul_comp, h]
    have hs := ((isWeilMorphism_rightDerivedLowerShriek_commShiftIso_inv sq
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ)
        f.geometricGaloisFrobenius.asIso.hom).hom
        (2 * d)).comp
        (ho.rightDerivedLowerShriek_map sq)).comp h3
    unfold IsWeilMorphism at hs ⊢
    rw [TateOrientation.untwistedSmoothTrace_ofUnit, Functor.map_comp, Category.assoc,
      ← Functor.map_comp_assoc _ E.hom, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    simp only [TateOrientation.unitTrace, Category.assoc] at hs ⊢
    rw [reassoc_of% hs]
  · -- Geometric Frobenius acts trivially on `End(Λ_{k̄}) = Λ`.
    have hY (v : 𝟙_ (DerivedCategoryModule Λ (Spec (.of (AlgebraicClosure k₀)))) ⟶ 𝟙_ _) :
        ∃ r : Λ, v = r • 𝟙 _ := by
      obtain ⟨r, hr⟩ := (bijective_smul_id_unit Λ (Spec (.of (AlgebraicClosure k₀)))).2 v
      exact ⟨r, hr.symm⟩
    have hv := frobeniusOperator_unit_eq_self σ hY (z ≫ E.inv)
    rw [frobeniusOperator_apply, Functor.map_comp, Category.assoc] at hv
    rw [frobeniusOperator_apply]
    simp only [Linear.comp_smul, Linear.smul_comp, ← Category.assoc] at hv ⊢
    simp only [Category.assoc] at hv ⊢
    rw [reassoc_of% hv, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Etale
