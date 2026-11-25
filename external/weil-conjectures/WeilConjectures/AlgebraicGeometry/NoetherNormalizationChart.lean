/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Finite flat charts of integral schemes of finite type over a field

Let `X` be an integral scheme locally of finite type over a field `k`. We show that `X` contains
a nonempty affine open `W` admitting a finite, flat morphism of finite presentation
`W ⟶ Spec k[X₁, …, X_d]_r` over `k`, for some nonzero polynomial `r`. The target is smooth and
geometrically irreducible over `k`.

## Strategy

Take a nonempty affine open `U = Spec B` of `X`. By Noether normalization `B` is finite over a
polynomial ring `A = k[X₁, …, X_d] ⊆ B`, and by generic freeness `B_r` is free over `A_r` for
some nonzero `r ∈ A`. Then `W = Spec B_r` is a basic open of `U`.

## Main results

- `AlgebraicGeometry.smooth_specMap_algebraMap_localizationAway`: `Spec k[X]_r` is smooth
  over `k`.
- `AlgebraicGeometry.geometricallyIrreducible_specMap_algebraMap_localizationAway`:
  `Spec k[X]_r` is geometrically irreducible over `k` for `r ≠ 0`.
- `AlgebraicGeometry.exists_finite_flat_chart`: the finite flat chart.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {d : ℕ}

/-- The spectrum of a localization `k[X₁, …, X_d]_r` of a polynomial ring is smooth over `k`. -/
theorem smooth_specMap_algebraMap_localizationAway (r : MvPolynomial (Fin d) k) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r)))) := by
  have : Algebra.Smooth k (Localization.Away r) :=
    ⟨Algebra.FormallySmooth.comp k (MvPolynomial (Fin d) k) _,
      .trans k (MvPolynomial (Fin d) k) _⟩
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr this)

/-- A morphism from a nonempty scheme to the spectrum of a field is surjective. -/
lemma surjective_of_nonempty_of_field {K : Type u} [Field K] {Y : Scheme.{u}} [Nonempty Y]
    (f : Y ⟶ Spec (.of K)) : Surjective f := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨x⟩ := ‹Nonempty Y›
  exact ⟨x, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩

/-- The spectrum of a localization `k[X₁, …, X_d]_r` of a polynomial ring at a nonzero `r` is
geometrically irreducible over `k`: it is a nonempty open subscheme of affine space. -/
theorem geometricallyIrreducible_specMap_algebraMap_localizationAway
    {r : MvPolynomial (Fin d) k} (hr : r ≠ 0) :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r)))) := by
  have : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
  have e : Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) =
      (Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin d) k) (Localization.Away r))) ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.renameEquiv k (Equiv.ulift.{u} (α := Fin d))).toRingHom) ≫
        (AffineSpace.SpecIso (ULift (Fin d)) (.of k)).inv) ≫
        𝔸(ULift (Fin d); Spec (.of k)) ↘ Spec (.of k) := by
    rw [Category.assoc, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext a
    simp [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k) (Localization.Away r)]
  have hs := surjective_of_nonempty_of_field
    (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))))
  have : IsIso (CommRingCat.ofHom
      (MvPolynomial.renameEquiv k (Equiv.ulift.{u} (α := Fin d))).toRingHom) :=
    (MvPolynomial.renameEquiv k
      (Equiv.ulift.{u} (α := Fin d))).toRingEquiv.toCommRingCatIso.isIso_hom
  rw [e] at hs ⊢
  infer_instance

/-- **Finite flat charts.** An integral scheme `X` locally of finite type over a field `k`
contains a nonempty affine open `W` together with a finite, flat morphism of finite presentation
`π : W ⟶ Spec k[X₁, …, X_d]_r` over `k`, for some nonzero `r`. -/
theorem exists_finite_flat_chart (X : Scheme.{u}) [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] :
    ∃ (W : Scheme.{u}) (j : W ⟶ X) (d : ℕ) (r : MvPolynomial (Fin d) k)
      (π : W ⟶ Spec (.of (Localization.Away r))),
      IsOpenImmersion j ∧ IsAffine W ∧ Nonempty W ∧ r ≠ 0 ∧ IsFinite π ∧ Flat π ∧
        LocallyOfFinitePresentation π ∧
        j ≫ sX = π ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Algebra k Γ(X, U) :=
    ((sX.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(X, U) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appLE @LocallyOfFiniteType sX ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top) (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k Γ(X, U)
  let : Algebra (MvPolynomial (Fin d) k) Γ(X, U) := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin d) k) Γ(X, U) := hfin
  obtain ⟨r, hr, hfree, -⟩ :=
    Module.Finite.exists_free_localizedModule_powers_of_isDomain
      (A := MvPolynomial (Fin d) k) (M := Γ(X, U))
  let B' := Localization (Algebra.algebraMapSubmonoid Γ(X, U) (.powers r))
  have hfin' : Module.Finite (Localization.Away r) B' :=
    Module.Finite.of_isLocalizedModule (.powers r)
      (IsScalarTower.toAlgHom (MvPolynomial (Fin d) k) Γ(X, U) B').toLinearMap
  have hflat : Module.Flat (Localization.Away r) B' :=
    Module.Flat.of_linearEquiv ((IsLocalizedModule.linearEquiv (.powers r)
      (LocalizedModule.mkLinearMap (.powers r) Γ(X, U))
      (IsScalarTower.toAlgHom (MvPolynomial (Fin d) k) Γ(X, U) B').toLinearMap
      ).extendScalarsOfIsLocalization (.powers r) (Localization.Away r)).symm
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin d) k) Γ(X, U) r) B' := by
    simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    infer_instance
  have hgr : algebraMap (MvPolynomial (Fin d) k) Γ(X, U) r ≠ 0 :=
    fun h ↦ hr (hg (h.trans (map_zero g).symm))
  have : IsDomain B' := IsLocalization.isDomain_localization (by
    rw [Algebra.algebraMapSubmonoid_powers]
    exact powers_le_nonZeroDivisors_of_noZeroDivisors hgr)
  have := IsOpenImmersion.of_isLocalization (algebraMap (MvPolynomial (Fin d) k) Γ(X, U) r)
    (S := B')
  refine ⟨Spec (.of B'), Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B')) ≫ hU.fromSpec,
    d, r, Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away r) B')), inferInstance,
    inferInstance, inferInstance, hr, (IsFinite.SpecMap_iff _).mpr
      (RingHom.finite_algebraMap.mpr hfin'), Flat.SpecMap_iff.mpr
      (RingHom.flat_algebraMap_iff.mpr hflat), HasRingHomProperty.Spec_iff.mpr
      (RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp inferInstance)), ?_⟩
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec sX (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  ext a
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k) (Localization.Away r),
    ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k) (Localization.Away r) B',
    IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k) Γ(X, U) B']
  congr 1
  exact (g.commutes a).symm

end AlgebraicGeometry
