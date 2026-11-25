/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# Restricting a constant ring sheaf to its constant scalars

## References

* Stacks Project, Tags 093I and 03CY
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) (B : Type u) [CommRing B]


/-- Restriction to constant scalars preserves the underlying additive sheaf exactly. -/
noncomputable def proEtaleModuleRestriction :
    proEtaleRingModules T (proEtaleConstantRing T B) ⥤
      Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars (proEtaleModuleScalarUnit T B)).obj M.val
    let F : T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} B) :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp (ProEt.topology T) F
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map φ := ⟨{
    app U := ((PresheafOfModules.restrictScalars
      (proEtaleModuleScalarUnit T B)).map φ.val).app U
    naturality _ _ f := by
      ext x
      exact ConcreteCategory.congr_hom (φ.val.naturality f) x }⟩
  map_id M := by ext U x; rfl
  map_comp φ ψ := by ext U x; rfl

private noncomputable def constantModulePresheaf :
    (T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} B)) ⥤
      PresheafOfModules.{u + 1}
        ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B))) where
  obj F :=
    { obj := F.obj
      map f := F.map f
      map_id U := by ext x; exact ConcreteCategory.congr_hom (F.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map φ :=
    { app := φ.app
      naturality f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }

private noncomputable def constantModuleFullyFaithful :
    (constantModulePresheaf T B).FullyFaithful where
  preimage φ :=
    { app := φ.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

private noncomputable instance : (constantModulePresheaf T B).Full :=
  (constantModuleFullyFaithful T B).full

private noncomputable instance : (constantModulePresheaf T B).Faithful :=
  (constantModuleFullyFaithful T B).faithful

private noncomputable def moduleEmbedding :=
  sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) ⋙
    constantModulePresheaf T B

private noncomputable instance : (moduleEmbedding T B).Full :=
  inferInstanceAs (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) ⋙ constantModulePresheaf T B).Full

private noncomputable instance : (moduleEmbedding T B).Faithful :=
  inferInstanceAs (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) ⋙ constantModulePresheaf T B).Faithful

private noncomputable instance scalarUnit_injective :
    Presheaf.IsLocallyInjective (ProEt.topology T) (proEtaleModuleScalarUnit T B) :=
  (proEtaleConstantRingUnit_locallyBijective T B).1

private noncomputable instance scalarUnit_surjective :
    Presheaf.IsLocallySurjective (ProEt.topology T) (proEtaleModuleScalarUnit T B) :=
  (proEtaleConstantRingUnit_locallyBijective T B).2

private noncomputable instance restriction_full : (proEtaleModuleRestriction T B).Full := by
  exact Functor.Full.of_comp_faithful_iso
    (G := moduleEmbedding T B)
    (H := SheafOfModules.forget _ ⋙
      PresheafOfModules.restrictScalars (proEtaleModuleScalarUnit T B)) (Iso.refl _)

private noncomputable instance restriction_faithful :
    (proEtaleModuleRestriction T B).Faithful := by
  exact Functor.Faithful.of_comp_iso
    (G := moduleEmbedding T B)
    (H := SheafOfModules.forget _ ⋙
      PresheafOfModules.restrictScalars (proEtaleModuleScalarUnit T B)) (Iso.refl _)

private noncomputable instance restriction_essSurj :
    (proEtaleModuleRestriction T B).EssSurj where
  mem_essImage F := by
    let P := (moduleEmbedding T B).obj F
    let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
      (proEtaleModuleScalarUnit T B)
    have hη : IsIso (adj.unit.app P) := by
      rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
      change IsIso (toSheafify (ProEt.topology T) P.presheaf)
      exact isIso_toSheafify (ProEt.topology T)
        ((sheafCompose (ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
            AddCommGrpCat.{u + 1})).obj F).property
    refine ⟨(PresheafOfModules.sheafification.{u + 1} (proEtaleModuleScalarUnit T B)).obj P, ⟨?_⟩⟩
    exact (Functor.FullyFaithful.ofFullyFaithful (moduleEmbedding T B)).preimageIso
      (asIso (adj.unit.app P)).symm

/-- Restricting to constant scalars is an equivalence of the two coefficient encodings. -/
theorem proEtaleModuleRestriction_isEquivalence :
    (proEtaleModuleRestriction T B).IsEquivalence := by
  exact {}

/-- The equivalence from intrinsic modules to fixed-coefficient sheaves. -/
noncomputable def proEtaleModuleEncoding :
    proEtaleRingModules T (proEtaleConstantRing T B) ≌
      Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) :=
  haveI := proEtaleModuleRestriction_isEquivalence T B
  (proEtaleModuleRestriction T B).asEquivalence

end AlgebraicGeometry.Scheme
