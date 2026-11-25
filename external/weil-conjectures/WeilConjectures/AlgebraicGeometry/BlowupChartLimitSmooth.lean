/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.BlowupChartLimitPushout
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.AffinePresentation

/-!
# Charts of blow-ups of surfaces étale over the plane are smooth surfaces

Let `k` be a ring and `g : k[X₀, X₁] → A` an étale ring map, with `x = g(X₀)`, `y = g(X₁)`. Then
the chart `A[T]/(xT - y)` is étale over `k[X₀, X₁]` via `X₀ ↦ x`, `X₁ ↦ T` (it is the base
change of `A` along the chart `X₁ ↦ X₀X₁` of the blow-up of the plane), hence every
localization `(A[T]/(xT - y))[1/u]` is standard smooth of relative dimension `2` over `k`
(`AlgebraicGeometry.isStandardSmoothOfRelativeDimension_blowupChart_away`).

We also record that affine changes of coordinates `X₀ ↦ X₀ + aX₁ + c₀`, `X₁ ↦ X₁ + c₁` of the
plane are automorphisms, so that they preserve étale coordinates
(`AlgebraicGeometry.etale_comp_affineSubst`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry

attribute [local instance] isStandardSmoothOfRelativeDimension_mvPolynomial

/-- Étale ring maps are stable under cobase change, in the form of pushout squares of commutative
rings. -/
lemma etale_of_isPushout {A B C D : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ D}
    {inr : C ⟶ D} (h : IsPushout f g inl inr) (hf : f.hom.Etale) : inr.hom.Etale := by
  have : (RingHom.toMorphismProperty RingHom.Etale).IsStableUnderCobaseChange :=
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).mpr
      RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (P := RingHom.toMorphismProperty RingHom.Etale) h.flip hf

section AffineSubst

variable {R₀ : Type u} [CommRing R₀]

/-- The affine change of coordinates `X₀ ↦ X₀ + aX₁ + c₀`, `X₁ ↦ X₁ + c₁` of the plane. -/
noncomputable def affineSubst (a c₀ c₁ : R₀) :
    MvPolynomial (Fin 2) R₀ →ₐ[R₀] MvPolynomial (Fin 2) R₀ :=
  aeval ![X 0 + C a * X 1 + C c₀, X 1 + C c₁]

/-- `affineSubst a c₀ c₁` sends `X₀` to `X₀ + aX₁ + c₀`. -/
@[simp]
lemma affineSubst_X_zero (a c₀ c₁ : R₀) : affineSubst a c₀ c₁ (X 0) = X 0 + C a * X 1 + C c₀ := by
  simp [affineSubst]

/-- `affineSubst a c₀ c₁` sends `X₁` to `X₁ + c₁`. -/
@[simp]
lemma affineSubst_X_one (a c₀ c₁ : R₀) : affineSubst a c₀ c₁ (X 1) = X 1 + C c₁ := by
  simp [affineSubst]

/-- `affineSubst a c₀ c₁` fixes the constants. -/
@[simp]
lemma affineSubst_C (a c₀ c₁ r : R₀) : affineSubst a c₀ c₁ (C r) = C r := by
  simp [affineSubst]

/-- The inverse affine change of coordinates, as a right inverse. -/
lemma affineSubst_comp_affineSubst_neg (a c₀ c₁ : R₀) :
    (affineSubst a c₀ c₁).comp (affineSubst (-a) (-c₀ + a * c₁) (-c₁)) = AlgHom.id _ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [affineSubst]
    ring
  · simp [affineSubst]

/-- The inverse affine change of coordinates, as a left inverse. -/
lemma affineSubst_neg_comp_affineSubst (a c₀ c₁ : R₀) :
    (affineSubst (-a) (-c₀ + a * c₁) (-c₁)).comp (affineSubst a c₀ c₁) = AlgHom.id _ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [affineSubst]
    ring
  · simp [affineSubst]

/-- Affine changes of coordinates of the plane are bijective. -/
lemma bijective_affineSubst (a c₀ c₁ : R₀) : Function.Bijective (affineSubst a c₀ c₁) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨affineSubst (-a) (-c₀ + a * c₁) (-c₁), ?_, ?_⟩
  · intro p
    exact congr($(affineSubst_neg_comp_affineSubst a c₀ c₁) p)
  · intro p
    exact congr($(affineSubst_comp_affineSubst_neg a c₀ c₁) p)

/-- Precomposing an étale ring map out of the plane with an affine change of coordinates gives an
étale ring map. -/
lemma etale_comp_affineSubst {A : Type u} [CommRing A] {g : MvPolynomial (Fin 2) R₀ →+* A}
    (hg : g.Etale) (a c₀ c₁ : R₀) : (g.comp (affineSubst a c₀ c₁).toRingHom).Etale :=
  RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (bijective_affineSubst _ _ _)) hg

end AffineSubst

/-- **Charts of the blow-up of a surface étale over the plane are smooth surfaces.** For an
étale ring map `g : k[X₀, X₁] → A` with `x = g(X₀)`, `y = g(X₁)` and any `u` in the chart
`A[T]/(xT - y)`, the localization `(A[T]/(xT - y))[1/u]` is standard smooth of relative
dimension `2` over `k`. -/
theorem isStandardSmoothOfRelativeDimension_blowupChart_away {k : Type u} [CommRing k]
    {A : CommRingCat.{u}} (g : CommRingCat.of (MvPolynomial (Fin 2) k) ⟶ A) (hg : g.hom.Etale)
    {x y : A} (hx : g.hom (X 0) = x) (hy : g.hom (X 1) = y) (uA : blowupChart x y) :
    ((algebraMap (blowupChart x y) (Localization.Away uA)).comp
      ((algebraMap A (blowupChart x y)).comp
        (g.hom.comp MvPolynomial.C))).IsStandardSmoothOfRelativeDimension 2 := by
  have hsq := isPushout_blowupChart_plane g x y hx hy
  have hψ : (planeToBlowupChart g x y).Etale := etale_of_isPushout hsq hg
  have heq : (algebraMap A (blowupChart x y)).comp (g.hom.comp MvPolynomial.C) =
      (planeToBlowupChart g x y).comp MvPolynomial.C := by
    ext r
    have := congr($(hsq.w).hom (MvPolynomial.C r))
    simpa [planeChartMap] using this
  rw [heq]
  have h₁ : (algebraMap (blowupChart x y)
      (Localization.Away uA)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway uA
  have h₂ : (planeToBlowupChart g x y).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.mp hψ
  have h₃ : (MvPolynomial.C : k →+* MvPolynomial (Fin 2) k).IsStandardSmoothOfRelativeDimension 2 :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 2).mpr inferInstance
  exact h₁.comp (h₂.comp h₃)

/-- The scheme version of `isStandardSmoothOfRelativeDimension_blowupChart_away`: the spectrum
of `(A[T]/(xT - y))[1/u]` is smooth of relative dimension `2` over `k`. -/
theorem smoothOfRelativeDimension_blowupChart_away {k : Type u} [CommRing k]
    {A : CommRingCat.{u}} (g : CommRingCat.of (MvPolynomial (Fin 2) k) ⟶ A) (hg : g.hom.Etale)
    {x y : A} (hx : g.hom (X 0) = x) (hy : g.hom (X 1) = y) (uA : blowupChart x y) :
    SmoothOfRelativeDimension 2 (Spec.map (CommRingCat.ofHom
      ((algebraMap (blowupChart x y) (Localization.Away uA)).comp
        ((algebraMap A (blowupChart x y)).comp (g.hom.comp MvPolynomial.C))))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 2)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    (isStandardSmoothOfRelativeDimension_blowupChart_away g hg hx hy uA)

end AlgebraicGeometry
