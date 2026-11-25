/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeNorm
public import WeilConjectures.AlgebraicGeometry.Divisor.Image
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Norms along finite locally free morphisms

Let `π : Y ⟶ X` be a finite morphism and `U` an affine open of `X` over which `Γ(Y, π⁻¹ U)` is a
free `Γ(X, U)`-module. Then the norm `Γ(Y, π⁻¹ U) ⟶ Γ(X, U)` (`AlgebraicGeometry.Scheme.Hom.normAt`)
detects non-vanishing along fibres: the norm of `a` does not vanish at `x ∈ U` if and only if `a`
does not vanish at any point over `x`.

Such affine opens exist around every point when `π` is finite, flat and locally of finite
presentation, and freeness is stable under base change.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_isAffineOpen_mem_free_app`: a finite flat morphism locally
  of finite presentation is free over a neighbourhood of every point of the target.
- `AlgebraicGeometry.free_app_of_isPullback`: freeness of the sections over an affine open is
  stable under base change.
- `AlgebraicGeometry.mem_basicOpen_normAt_of_free`: the non-vanishing locus of a norm.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

/-- **Finite locally free morphisms are free locally on the target.** If `p : X ⟶ Y` is finite,
flat and locally of finite presentation, every point `y` of `Y` has an affine open neighbourhood
`W` such that `Γ(X, p⁻¹ W)` is a free `Γ(Y, W)`-module. -/
lemma Scheme.Hom.exists_isAffineOpen_mem_free_app {X Y : Scheme.{u}} (p : X ⟶ Y) [IsFinite p]
    [Flat p] [LocallyOfFinitePresentation p] (y : Y) :
    ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧
      letI := (p.app W).hom.toAlgebra
      Module.Free Γ(Y, W) Γ(X, p ⁻¹ᵁ W) := by
  obtain ⟨W₀, hW₀, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have hX₀ : IsAffineOpen (p ⁻¹ᵁ W₀) := hW₀.preimage p
  let : Algebra Γ(Y, W₀) Γ(X, p ⁻¹ᵁ W₀) := (p.app W₀).hom.toAlgebra
  have : Module.Finite Γ(Y, W₀) Γ(X, p ⁻¹ᵁ W₀) := p.finite_app W₀ hW₀
  have hflat : (p.app W₀).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE @Flat p inferInstance ⟨W₀, hW₀⟩ ⟨_, hX₀⟩ _
  have : Module.Flat Γ(Y, W₀) Γ(X, p ⁻¹ᵁ W₀) := hflat
  have hfp : (p.app W₀).hom.FinitePresentation := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE @LocallyOfFinitePresentation p inferInstance ⟨W₀, hW₀⟩
      ⟨_, hX₀⟩ _
  have : Algebra.FinitePresentation Γ(Y, W₀) Γ(X, p ⁻¹ᵁ W₀) := hfp
  have : Module.FinitePresentation Γ(Y, W₀) Γ(X, p ⁻¹ᵁ W₀) :=
    .of_finite_of_finitePresentation _ _
  obtain ⟨z, rfl⟩ : y ∈ Set.range hW₀.fromSpec := by rwa [hW₀.range_fromSpec]
  obtain ⟨r, hr, hfree, -⟩ := Module.exists_free_localizedModule_powers_of_flat
    (R := Γ(Y, W₀)) (M := Γ(X, p ⁻¹ᵁ W₀)) z.asIdeal
  refine ⟨Y.basicOpen r, hW₀.basicOpen r, (hW₀.fromSpec_mem_basicOpen_iff z r).mpr hr, ?_⟩
  have hle : p ⁻¹ᵁ Y.basicOpen r ≤ p ⁻¹ᵁ W₀ := p.preimage_mono (Y.basicOpen_le r)
  let : Algebra Γ(Y, Y.basicOpen r) Γ(X, p ⁻¹ᵁ Y.basicOpen r) :=
    (p.app (Y.basicOpen r)).hom.toAlgebra
  let : Algebra Γ(X, p ⁻¹ᵁ W₀) Γ(X, p ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  let : Algebra Γ(Y, W₀) Γ(X, p ⁻¹ᵁ Y.basicOpen r) :=
    (p.app W₀ ≫ X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have : IsScalarTower Γ(Y, W₀) Γ(X, p ⁻¹ᵁ W₀) Γ(X, p ⁻¹ᵁ Y.basicOpen r) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, W₀) Γ(Y, Y.basicOpen r) Γ(X, p ⁻¹ᵁ Y.basicOpen r) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra]
      exact congrArg CommRingCat.Hom.hom (p.naturality _).symm)
  have : IsLocalization.Away r Γ(Y, Y.basicOpen r) := hW₀.isLocalization_basicOpen r
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, p ⁻¹ᵁ W₀) (Submonoid.powers r))
      Γ(X, p ⁻¹ᵁ Y.basicOpen r) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    have e : p ⁻¹ᵁ Y.basicOpen r = X.basicOpen (p.app W₀ r) := Scheme.preimage_basicOpen p r
    have := hX₀.isLocalization_basicOpen (p.app W₀ r)
    let ψ := (X.presheaf.mapIso (eqToIso e).op).commRingCatIsoToRingEquiv
    refine IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (p.app W₀ r))
      { ψ with commutes' := fun x ↦ ?_ }
    change (X.presheaf.map _ ≫ X.presheaf.map _) x = X.presheaf.map _ x
    rw [← Functor.map_comp]
    rfl
  exact Module.free_of_isLocalizedModule_away_of_dvd (dvd_refl r) Γ(Y, Y.basicOpen r)
    (IsScalarTower.toAlgHom Γ(Y, W₀) Γ(X, p ⁻¹ᵁ W₀) Γ(X, p ⁻¹ᵁ Y.basicOpen r)).toLinearMap

/-- **Freeness is stable under base change.** Consider a pullback square
```
  Y --g--> X
  |        |
  iY       iX
  v        v
  T --f--> S
```
and affine opens `US` of `S`, `UX ⊆ iX⁻¹ US` of `X` such that `f⁻¹ US` is affine. If
`Γ(T, f⁻¹ US)` is a free `Γ(S, US)`-module, then `Γ(Y, g⁻¹ UX)` is a free `Γ(X, UX)`-module. -/
lemma free_app_of_isPullback {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S}
    {iY : Y ⟶ T} (H : IsPullback g iY iX f) {US : S.Opens} {UX : X.Opens}
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen (f ⁻¹ᵁ US)) (hUX : IsAffineOpen UX)
    (hUSX : UX ≤ iX ⁻¹ᵁ US)
    (hfree : letI := (f.app US).hom.toAlgebra; Module.Free Γ(S, US) Γ(T, f ⁻¹ᵁ US)) :
    letI := (g.app UX).hom.toAlgebra
    Module.Free Γ(X, UX) Γ(Y, g ⁻¹ᵁ UX) := by
  have hUY : g ⁻¹ᵁ UX = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ (f ⁻¹ᵁ US) := by
    refine (inf_eq_left.mpr fun x hx ↦ ?_).symm
    have h₁ : iX (g x) ∈ US := hUSX hx
    rwa [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply] at h₁
  have := isIso_pushoutSection_of_isAffineOpen H (UT := f ⁻¹ᵁ US) le_rfl hUSX hUY hUS hUT hUX
  have hpo := (isIso_pushoutSection_iff ..).mp this
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at hpo
  let : Algebra Γ(S, US) Γ(X, UX) := (iX.appLE US UX hUSX).hom.toAlgebra
  let : Algebra Γ(S, US) Γ(T, f ⁻¹ᵁ US) := (f.app US).hom.toAlgebra
  let : Algebra Γ(X, UX) Γ(Y, g ⁻¹ᵁ UX) := (g.app UX).hom.toAlgebra
  let : Algebra Γ(T, f ⁻¹ᵁ US) Γ(Y, g ⁻¹ᵁ UX) :=
    (iY.appLE (f ⁻¹ᵁ US) (g ⁻¹ᵁ UX) (hUY.le.trans inf_le_right)).hom.toAlgebra
  let : Algebra Γ(S, US) Γ(Y, g ⁻¹ᵁ UX) := (iX.appLE US UX hUSX ≫ g.app UX).hom.toAlgebra
  have : IsScalarTower Γ(S, US) Γ(X, UX) Γ(Y, g ⁻¹ᵁ UX) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, US) Γ(T, f ⁻¹ᵁ US) Γ(Y, g ⁻¹ᵁ UX) :=
    .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hpo.w)
  have hpush : Algebra.IsPushout Γ(S, US) Γ(T, f ⁻¹ᵁ US) Γ(X, UX) Γ(Y, g ⁻¹ᵁ UX) :=
    CommRingCat.isPushout_iff_isPushout.mp hpo.flip
  exact .of_equiv hpush.symm.equiv.toLinearEquiv

/-- **The non-vanishing locus of a norm.** Let `π : Y ⟶ X` be finite and `U` an affine open of
`X` such that `Γ(Y, π⁻¹ U)` is a free `Γ(X, U)`-module. For `a ∈ Γ(Y, π⁻¹ U)`, the norm of `a`
does not vanish at `x ∈ U` if and only if `a` does not vanish at any point over `x`. -/
lemma mem_basicOpen_normAt_of_free {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] {U : X.Opens}
    (hU : IsAffineOpen U)
    (hfree : letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U))
    (a : Γ(Y, π ⁻¹ᵁ U)) {x : X} (hx : x ∈ U) :
    x ∈ X.basicOpen (π.normAt U a) ↔ ∀ y, π y = x → y ∈ Y.basicOpen a := by
  have hV : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  obtain ⟨z, rfl⟩ : x ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  have hpt (w : Spec Γ(Y, π ⁻¹ᵁ U)) :
      π (hV.fromSpec w) = hU.fromSpec (PrimeSpectrum.comap (π.app U).hom w) := by
    have := congrArg (fun g ↦ g w) (IsAffineOpen.SpecMap_appLE_fromSpec π hU hV le_rfl)
    simp only [Scheme.Hom.comp_apply, Spec.map_apply] at this
    rw [← this, ← Scheme.Hom.app_eq_appLE]
  rw [hU.fromSpec_mem_basicOpen_iff]
  let := (π.app U).hom.toAlgebra
  have : Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := π.finite_app U hU
  refine (Algebra.norm_notMem_iff z.asIdeal a).trans ⟨fun h y hy ↦ ?_, fun h Q hQ hQz ↦ ?_⟩
  · obtain ⟨w, rfl⟩ : y ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      change π y ∈ U
      rw [hy]
      exact (Set.ext_iff.mp hU.range_fromSpec _).mp ⟨z, rfl⟩
    rw [hV.fromSpec_mem_basicOpen_iff]
    refine h w.asIdeal w.isPrime ?_
    rw [hpt] at hy
    exact congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective hy)
  · have := h (hV.fromSpec ⟨Q, hQ⟩) (by
      rw [hpt]
      congr 1
      exact PrimeSpectrum.ext hQz)
    rwa [hV.fromSpec_mem_basicOpen_iff] at this

end AlgebraicGeometry
