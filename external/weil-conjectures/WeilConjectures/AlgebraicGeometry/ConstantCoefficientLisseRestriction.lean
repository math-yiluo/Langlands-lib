/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientLocalModelsComparison

/-! # Surjective coefficient restriction preserves finite local constant modules

Source: Stacks Project, Cohomology on Sites, Tags 06YY and 094I.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules

private noncomputable def constantRingMap
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    {B D : Type u} [CommRing B] [CommRing D] (f : B →+* D) :
    constantCoefficientRing T B ⟶ constantCoefficientRing T D :=
  (sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).map
    ((constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom f))

private noncomputable def constantRestrictionIso
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    {B D : Type u} [CommRing B] [CommRing D] (f : B →+* D)
    (M : ModuleCat.{u} D) :
    (constantCoefficientModule T B).obj ((ModuleCat.restrictScalars f).obj M) ≅
      (restrictScalars (constantRingMap T f)).obj ((constantCoefficientModule T D).obj M) := by
  let f₀ : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶
      (Functor.const Cᵒᵖ).obj (RingCat.of D) :=
    (Functor.const Cᵒᵖ).map (RingCat.ofHom f)
  have hsq : f₀ ≫ constantCoefficientUnit T D =
      constantCoefficientUnit T B ≫ (constantRingMap T f).hom := by
    exact congrArg (fun η ↦ Functor.whiskerRight η (forget₂ CommRingCat.{u} RingCat.{u}))
      (toSheafify_naturality T
        ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom f)))
  let P := (strictPerfectConstantPresheaf (C := C) D).obj M
  let e : ((PresheafOfModules.restrictScalars f₀).obj P) ≅
      (strictPerfectConstantPresheaf (C := C) B).obj
        ((ModuleCat.restrictScalars f).obj M) := Iso.refl _
  have := restrictSheafificationComparison_isIso T
    (constantCoefficientUnit T B) (constantCoefficientUnit T D) f₀
    (constantRingMap T f) hsq P
  exact (PresheafOfModules.sheafification (constantCoefficientUnit T B)).mapIso e.symm ≪≫
    asIso (restrictSheafificationComparison T
      (constantCoefficientUnit T B) (constantCoefficientUnit T D) f₀
      (constantRingMap T f) hsq P)

/-- Restriction along a surjective coefficient homomorphism preserves local constant
finite-module descriptions. Source: Stacks Project, Cohomology on Sites, Tag 094I,
restriction of scalars in the filtration argument
(auxiliary; not a blueprint node).

Proof: coefficient restriction commutes with module sheafification, as shown by
the sheafification adjunction; its comparison is the identity on the associated
additive-group sheaves. It also commutes with restriction to each slice. Restrict
each constant finite local model along f. A finite D-module is finite over B,
since the surjection makes D a finite B-module. The same covering sieves and the
transported local isomorphisms give the required descriptions. -/
theorem locallyConstantFiniteTypeModules_restrictScalars_surjective
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    {B D : Type u} [CommRing B] [CommRing D] (f : B →+* D)
    (hf : Function.Surjective f)
    (F : SheafOfModules.{u} (constantCoefficientRing T D))
    (h : IsLocallyConstantFiniteTypeModules T D F) :
    IsLocallyConstantFiniteTypeModules T B ((restrictScalars ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((constantSheaf T CommRingCat.{u}).map (CommRingCat.ofHom f)))).obj F) := by
  intro V
  obtain ⟨S, hS, hs⟩ := h V
  refine ⟨S, hS, ?_⟩
  intro U g hg
  obtain ⟨M, hM, ⟨i⟩⟩ := hs U g hg
  let N := (ModuleCat.restrictScalars f).obj M
  let := f.toAlgebra
  let : Module D N := inferInstanceAs (Module D M)
  let : IsScalarTower B D N :=
    ⟨fun b d m ↦ by
      change (f b * d) • (show M from m) = f b • (d • (show M from m))
      exact mul_smul (f b) d m⟩
  have : Module.Finite D N := hM
  have : Module.Finite B D := RingHom.Finite.of_surjective f hf
  have hN : Module.Finite B N := Module.Finite.trans D N
  let α := constantRingMap T f
  let αU := (Functor.sheafPushforwardContinuous (Over.forget U) RingCat.{u}
    (T.over U) T).map α
  let c : ((restrictScalars α).obj F).over U ≅
      (restrictScalars αU).obj (F.over U) := Iso.refl _
  refine ⟨N, hN, ⟨c ≪≫ (restrictScalars αU).mapIso i ≪≫ ?_⟩⟩
  exact ((overFunctor _ U).mapIso (constantRestrictionIso T f M)).symm

end SheafOfModules
