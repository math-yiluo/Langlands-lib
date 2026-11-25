/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Mathlib.RingTheory.Flat.Stability

/-!
# Transport of flatness over the base

Flatness of an `𝒪_X`-module over the base (`AlgebraicGeometry.Scheme.Modules.IsFlatOver`) is
invariant under isomorphisms of modules, passes to the pullback along an open immersion into the
source, and can be checked after composing with an open immersion of the base.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- **Semilinear transport of flatness.** Let `φ : R →+* A` and `ψ : R' →+* B` be ring maps, `M`
an `A`-module and `N` a `B`-module, regarded as an `R`- resp. `R'`-module by restriction of
scalars. If `σ : R →+* R'` is bijective and `u : M →+ N` is bijective with
`u (φ r • m) = ψ (σ r) • u m`, then flatness of `M` over `R` implies flatness of `N` over `R'`. -/
theorem Module.Flat.of_bijective_compHom {R R' A B M N : Type*} [CommRing R] [CommRing R']
    [CommRing A] [CommRing B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (φ : R →+* A) (ψ : R' →+* B) (σ : R →+* R') (hσ : Function.Bijective σ) (u : M →+ N)
    (hu : Function.Bijective u) (hsmul : ∀ (r : R) (m : M), u (φ r • m) = ψ (σ r) • u m)
    (h : letI := Module.compHom M φ; Module.Flat R M) :
    letI := Module.compHom N ψ; Module.Flat R' N := by
  let := Module.compHom M φ
  let := Module.compHom N ψ
  let e : R ≃+* R' := RingEquiv.ofBijective σ hσ
  let : Module R N := Module.compHom N (ψ.comp σ)
  -- `N` is flat over `R`, being isomorphic to `M`.
  have : Module.Flat R N := Module.Flat.of_linearEquiv
    ({ AddEquiv.ofBijective u hu with map_smul' := hsmul } : M ≃ₗ[R] N).symm
  let : Algebra R' R := e.symm.toRingHom.toAlgebra
  have : IsScalarTower R' R N := ⟨fun r' r n ↦ (congrArg (· • n) ((congrArg ψ
    ((map_mul e _ _).trans (congrArg (· * e r) (e.apply_symm_apply r')))).trans
      (map_mul ψ _ _))).trans (mul_smul _ _ _)⟩
  -- `R` is flat over `R'`, being isomorphic to it.
  have : Module.Flat R' R := Module.Flat.of_linearEquiv
    ({ e.toAddEquiv with
        map_smul' := fun r' r ↦
          (map_mul e _ _).trans (congrArg (· * e r) (e.apply_symm_apply r')) } : R ≃ₗ[R'] R')
  exact Module.Flat.trans R' R N

namespace AlgebraicGeometry.Scheme.Modules

variable {X X' T T' : Scheme.{u}}

/-- Flatness over the base is invariant under isomorphisms of modules. -/
theorem IsFlatOver.of_iso {ℱ ℱ' : X.Modules} (e : ℱ ≅ ℱ') {f : X ⟶ T} (h : ℱ.IsFlatOver f) :
    ℱ'.IsFlatOver f := by
  intro V U hUV
  exact Module.Flat.of_bijective_compHom (f.appLE V.1 U.1 hUV).hom (f.appLE V.1 U.1 hUV).hom
    (RingHom.id _) Function.bijective_id (e.hom.app U.1).hom
    (ConcreteCategory.bijective_of_isIso (e.hom.app U.1)) (fun _ _ ↦ Hom.app_smul _ _ _)
    (h V U hUV)

/-- Flatness over the base passes to the pullback along an open immersion into the source. -/
theorem IsFlatOver.pullback_of_isOpenImmersion {ℱ : X.Modules} {f : X ⟶ T} (h : ℱ.IsFlatOver f)
    (j : X' ⟶ X) [IsOpenImmersion j] : ((Modules.pullback j).obj ℱ).IsFlatOver (j ≫ f) := by
  rintro V ⟨U', hU'⟩ hUV
  obtain ⟨W, hW, hWr, hWV, rfl⟩ : ∃ W : X.Opens, IsAffineOpen W ∧ W ≤ j.opensRange ∧
      W ≤ f ⁻¹ᵁ V.1 ∧ j ⁻¹ᵁ W = U' :=
    ⟨j ''ᵁ U', hU'.image_of_isOpenImmersion j, Set.image_subset_range _ _,
      fun _ ⟨_, hy, hx⟩ ↦ hx ▸ hUV hy, j.preimage_image_eq U'⟩
  refine Module.Flat.of_bijective_compHom (f.appLE V.1 W hWV).hom
    ((j ≫ f).appLE V.1 (j ⁻¹ᵁ W) hUV).hom (RingHom.id _) Function.bijective_id
    (pullbackUnitApp j ℱ W).hom (bijective_pullbackUnit_app_of_isOpenImmersion j ℱ hWr)
    (fun r m ↦ ?_) (h V ⟨W, hW⟩ hWV)
  rw [RingHom.id_apply, ← Scheme.Hom.appLE_comp_appLE j f V.1 W (j ⁻¹ᵁ W) hWV le_rfl,
    Scheme.Hom.appLE_eq_app, CommRingCat.comp_apply]
  exact Hom.app_smul _ _ _

/-- Flatness over the base can be checked after composing with an open immersion of the base. -/
theorem IsFlatOver.of_comp_isOpenImmersion {ℱ : X.Modules} {f : X ⟶ T} (ι : T ⟶ T')
    [IsOpenImmersion ι] (h : ℱ.IsFlatOver (f ≫ ι)) : ℱ.IsFlatOver f := by
  intro V U hUV
  have hUV' : U.1 ≤ (f ≫ ι) ⁻¹ᵁ (ι ''ᵁ V.1) := by
    intro x hx
    exact ⟨f x, hUV hx, rfl⟩
  refine Module.Flat.of_bijective_compHom ((f ≫ ι).appLE _ U.1 hUV').hom
    (f.appLE V.1 U.1 hUV).hom (ι.appIso V.1).hom.hom
    (ConcreteCategory.bijective_of_isIso (ι.appIso V.1).hom) (AddMonoidHom.id _)
    Function.bijective_id (fun r m ↦ ?_) (h ⟨_, V.2.image_of_isOpenImmersion ι⟩ U hUV')
  rw [AddMonoidHom.id_apply, AddMonoidHom.id_apply, Scheme.Hom.appIso_hom',
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

end AlgebraicGeometry.Scheme.Modules
