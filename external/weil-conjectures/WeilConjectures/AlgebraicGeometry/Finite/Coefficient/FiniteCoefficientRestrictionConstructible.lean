/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus

/-! # Finite coefficient restriction preserves constructibility

Source: blueprint latest, uniform constructible Ext, finite-basis restriction argument.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

private theorem free_restricted_regular_map
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [MonoidalCategory D] [MonoidalPreadditive D]
    (F : C ⥤ D) [F.LaxMonoidal] [F.Additive] [PreservesFiniteColimits F]
    {R S : C} [MonObj R] [MonObj S]
    [PreservesFiniteColimits (tensorLeft R)]
    [PreservesFiniteColimits (tensorLeft (F.obj R))]
    (φ : R ⟶ S) [IsMonHom φ]
    (h : Mod.IsFree R ((Mod.comap φ).obj (Mod.regular S))) :
    Mod.IsFree (F.obj R) ((Mod.comap (F.map φ)).obj (Mod.regular (F.obj S))) := by
  have : (F.mapMod R).Additive := ⟨by intros; ext; exact F.map_add⟩
  exact (h.map (F.mapMod R) (Iso.refl _)).of_iso
    ((F.mapModComapIso φ).app (Mod.regular S))

private theorem constructible_restrict_of_free
    {X : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ]
    (hfree : Mod.IsFree R ((Mod.comap φ).obj (Mod.regular S)))
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (hM : IsConstructibleModuleObject S M) :
    IsConstructibleModuleObject R ((Mod.comap φ).obj M) := by
  obtain ⟨T, hT⟩ := hM
  refine ⟨T, fun a ↦ ?_⟩
  let F := ProEtale.upperStar Ab.{u + 1} (T.immersion a)
  let M' := (F.mapMod S).obj M
  have hF := free_restricted_regular_map F φ hfree
  obtain ⟨U, hU⟩ := hT a
  refine ⟨U, fun i ↦ ?_⟩
  let G := ProEtale.upperStar Ab.{u + 1} (U.f i)
  have hG := free_restricted_regular_map G (F.map φ) hF
  have hfp := (hU i).map_of_isFree (Mod.comap (G.map (F.map φ))) hG
  exact hfp.of_iso
    (((G.mapModComapIso (F.map φ)).app M').symm ≪≫
      (G.mapMod (F.obj R)).mapIso (((F.mapModComapIso φ).app M).symm))

namespace AlgebraicGeometry.ProEtale

/-- Restricting a constructible sheaf along an inclusion of finite coefficient fields
preserves the upstream local finite presentation predicate.

Source: blueprint latest, sk-lem-uniform-constructible-ext.proof.md, algebraic-closure
coefficient argument. (blueprint: lem-sfb-finite-coefficient-restriction-constructible).

Proof: choose a basis of F over E. Its continuous coordinates identify the restricted
regular F coefficient module with a finite free E coefficient module. Inverse image
preserves this identification on every stratum and every member of its presentation
cover. Exact additive restriction takes a presentation F^m -> F^n -> M -> 0 to
E^(m[F:E]) -> E^(n[F:E]) -> Res M -> 0. Use the same stratification and covers.
The empty stratification and the zero module require no separate choices. -/
theorem finiteCoefficientRestriction_constructible
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F))
    (hM : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ F) M) :
    IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E)
      ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj M) := by
  obtain ⟨e⟩ := (condensedFiniteCoefficientCalculus X ℓ h).1
  exact constructible_restrict_of_free _ ⟨_, ⟨e⟩⟩ hM

end AlgebraicGeometry.ProEtale
