/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Free affine neighbourhoods for a finite flat morphism

## References

* Stacks Project, Tag 0BVH, construction before Lemma 49.3.1
* Tags 02K9 and 00NX
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite flat section algebra has a finite basis near every target point. -/
theorem exists_affine_basis_of_finite_flat
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧
      (letI := (f.app U.1).hom.toAlgebra
       ∃ n : ℕ, Nonempty (Module.Basis (Fin n) Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  let A := Γ(Y, W)
  let B := Γ(X, f ⁻¹ᵁ W)
  let := (f.app W).hom.toAlgebra
  have hXW : IsAffineOpen (f ⁻¹ᵁ W) := hW.preimage f
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : Module.Finite A B := f.finite_app W hW
  have : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  have : Module.Flat A B := by
    have hf := f.flat_appLE hW hXW le_rfl
    rwa [← Hom.app_eq_appLE] at hf
  let p := hW.primeIdealOf ⟨y, hyW⟩
  have : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl B) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl B)
    (Localization.AtPrime p.asIdeal)
  have hyr : y ∈ Y.basicOpen r := by
    have hp : p ∈ PrimeSpectrum.basicOpen r := hr
    have := (hW.fromSpec_preimage_basicOpen r).ge hp
    change hW.fromSpec p ∈ Y.basicOpen r at this
    rwa [hW.fromSpec_primeIdealOf] at this
  let U := Y.affineBasicOpen (U := ⟨W, hW⟩) r
  let Ar := Γ(Y, U.1)
  let Br := Γ(X, f ⁻¹ᵁ U.1)
  let := (f.app U.1).hom.toAlgebra
  let : Algebra A Ar :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  have hAr : IsLocalization.Away r Ar := hW.isLocalization_basicOpen r
  let : Algebra B Br := (X.presheaf.map
    (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have hBr : IsLocalization.Away (algebraMap A B r) Br :=
    hXW.isLocalization_of_eq_basicOpen (algebraMap A B r) _ (by
      change f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.app W r)
      exact Scheme.preimage_basicOpen f r)
  let : Algebra A Br := ((algebraMap B Br).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B Br := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A Ar Br := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (f.naturality (homOfLE (Y.basicOpen_le r)).op)) a).symm)
  let l : B →ₗ[A] Br := (IsScalarTower.toAlgHom A B Br).toLinearMap
  have : IsLocalizedModule (.powers r) l := by
    apply isLocalizedModule_iff_isLocalization.mpr
    simpa only [Algebra.algebraMapSubmonoid_powers] using hBr
  let eR := IsLocalization.algEquiv (.powers r) (Localization.Away r) Ar
  let : Algebra (Localization.Away r) Ar := eR.toRingHom.toAlgebra
  have : IsScalarTower A (Localization.Away r) Ar :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact (eR.commutes a).symm)
  let : Module (Localization.Away r) Br := Module.compHom Br eR.toRingHom
  have : IsScalarTower A (Localization.Away r) Br :=
    IsScalarTower.of_algebraMap_smul (fun a x ↦ by
      change eR (algebraMap A (Localization.Away r) a) • x = a • x
      rw [eR.commutes, IsScalarTower.algebraMap_smul])
  let e := IsLocalizedModule.iso (.powers r) l
  let e' := e.extendScalarsOfIsLocalization (.powers r) (Localization.Away r)
  have : RingHomInvPair eR.toRingHom eR.symm.toRingHom := ⟨by ext; simp, by ext; simp⟩
  have : RingHomInvPair eR.symm.toRingHom eR.toRingHom := ⟨by ext; simp, by ext; simp⟩
  let e'' : LocalizedModule.Away r B ≃ₛₗ[eR.toRingHom] Br :=
    { __ := e.toAddEquiv
      map_smul' := e'.map_smul }
  have := hfree
  have : Module.Free Ar Br := Module.Free.of_equiv e''
  have : Nontrivial Ar := (U.2.primeIdealOf ⟨y, hyr⟩).nontrivial
  have : Module.Finite Ar Br := f.finite_app U.1 U.2
  exact ⟨U, hyr, Module.finrank Ar Br, ⟨Module.finBasis Ar Br⟩⟩

end AlgebraicGeometry.Scheme
