/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FlatRingedDiagramInput.FlatRingedDiagramRestrictionDefs
public import WeilConjectures.CategoryTheory.ExactAdjointTowerModels.ExactAdjointTowerModels
import WeilConjectures.Algebra.Homology.ProperBaseChange.FlatRestrictionExactLeftAdjoint
import WeilConjectures.CategoryTheory.ProperBaseChange.SmallModuleDiagramsGrothendieck
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Flat scalars and the normalized direct-image/strict-limit square

Source: blueprint main-20261015, proper base change, completed exchange coherence,
second paragraph; scalar supplement using Stacks Tags 0A07, 08BJ, 070I, 070Y and 070K
(blueprint: lem-weil-pbc-flat-scalar-tower-limit-square).

The auxiliary structures merely bundle the universal units and their normalization
identities. Ordinary scalar-limit maps are fixed by `limit.post`, which sends a
compatible family to the same family. Positive tower level n+1 is indexed by n : ℕ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w uA uB uA' uB' vA vB vA' vB'

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ExactAdjointTowerModels

namespace CategoryTheory.FlatScalarTowerLimit

-- Infer the category from the equation before elaborating its common final factor.
private theorem map_three
    {E : Type uA} [Category.{vA} E] {T : Type uB} [Category.{vB} T]
    (F : E ⥤ T) {X Y Z W : E} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    F.map (f ≫ g ≫ h) = F.map f ≫ F.map g ≫ F.map h := by
  rw [F.map_comp, F.map_comp]

-- Comparisons can be descended directly from the two units on K-injectives.
private theorem normalized_iso
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {T : Type uB} [Category.{vB} T]
    (F : CochainComplex A ℤ ⥤ T) (P R : DerivedCategory A ⥤ T)
    (a : F ⟶ DerivedCategory.Q ⋙ P) (b : F ⟶ DerivedCategory.Q ⋙ R)
    (ha : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (a.app I))
    (hb : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (b.app I)) :
    ∃ e : P ≅ R, ∀ I, a.app I ≫ e.hom.app (DerivedCategory.Q.obj I) = b.app I := by
  have h : (CochainComplex.KInjectives.localizerMorphism A).Derives F := by
    intro I J f hf
    have := I.property
    have := J.property
    have : QuasiIso f.hom := hf
    have := ha I.obj I.property
    have := ha J.obj J.property
    have he : F.map f.hom = a.app I.obj ≫ P.map (DerivedCategory.Q.map f.hom) ≫
        inv (a.app J.obj) := by
      have hn := a.naturality f.hom
      dsimp only [Functor.comp_map] at hn
      apply (cancel_mono (a.app J.obj)).mp
      simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hn
    change IsIso (F.map f.hom)
    rw [he]
    infer_instance
  have := h.isRightDerivedFunctor_of_isIso a (fun I ↦ ha I.obj I.property)
  have := h.isRightDerivedFunctor_of_isIso b (fun I ↦ hb I.obj I.property)
  refine ⟨Functor.rightDerivedUnique P R a b (HomologicalComplex.quasiIso A (.up ℤ)), ?_⟩
  intro I
  simpa only [Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
    Functor.rightDerivedNatTrans_app P R a b
    (HomologicalComplex.quasiIso A (.up ℤ)) (𝟙 F) I

private theorem derived_ext
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {T : Type uB} [Category.{vB} T]
    {P R : DerivedCategory A ⥤ T} (a b : P ⟶ R)
    (h : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      a.app (DerivedCategory.Q.obj I) = b.app (DerivedCategory.Q.obj I)) : a = b := by
  apply NatTrans.ext
  funext Z
  let K := DerivedCategory.Q.objPreimage Z
  obtain ⟨I, hI, f, _, hf⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  have := hf
  let e : Z ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso Z).symm ≪≫ asIso (DerivedCategory.Q.map f)
  apply (cancel_mono (R.map e.hom)).mp
  rw [← a.naturality, ← b.naturality, h I hI]

section Normalizations

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']

/-- The ordinary and derived scalar comparison, retaining both exact-localization
factors and the equation with universal right-derived units on K-injectives.
Source: Stacks Tags 070I, 070Y and 070K, scalar supplement to completed exchange coherence
(blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
structure ScalarComparison
    (F' : A' ⥤ B') (F : A ⥤ B) (r : A' ⥤ A) (s : B' ⥤ B)
    [F'.Additive] [F.Additive] [r.Additive] [s.Additive]
    (rD : DerivedCategory A' ⥤ DerivedCategory A)
    (sD : DerivedCategory B' ⥤ DerivedCategory B)
    (qr : DerivedCategory.Q ⋙ rD ≅ r.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qs : DerivedCategory.Q ⋙ sD ≅ s.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (M' : DerivedModel (F'.mapHomologicalComplex (.up ℤ)))
    (M : DerivedModel (F.mapHomologicalComplex (.up ℤ))) where
  ordinary : F' ⋙ s ≅ r ⋙ F
  derived : M'.functor ⋙ sD ≅ rD ⋙ M.functor
  normalized : ∀ I : CochainComplex A' ℤ, I.IsKInjective →
    sD.map (M'.unit.app I) ≫ derived.hom.app (DerivedCategory.Q.obj I) ≫
        M.functor.map (qr.hom.app I) =
      qs.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app I) ≫
        M.unit.app ((r.mapHomologicalComplex (.up ℤ)).obj I)

/-- The additive structure of ordinary limit, supplied by Mathlib's limit-preservation
criterion, so additivity is not an extra hypothesis of the scalar square.
Source: Stacks Tag 02MZ (blueprint: lem-weil-pbc-flat-scalar-tower-limit-square). -/
abbrev limitAdditive {E : Type uA} [Category.{vA} E] [Abelian E]
    [HasLimitsOfShape ℕᵒᵖ E] :
    (lim : (ℕᵒᵖ ⥤ E) ⥤ E).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [instance] limitAdditive

variable [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

end Normalizations

private theorem ordinary_square
    {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
    [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasLimitsOfShape ℕᵒᵖ A'] [HasLimitsOfShape ℕᵒᵖ B']
    (F' : A' ⥤ B') (F : A ⥤ B) (r : A' ⥤ A) (s : B' ⥤ B)
    (c : F' ⋙ s ≅ r ⋙ F)
    (d : (Functor.whiskeringRight ℕᵒᵖ A' B').obj F' ⋙
        (Functor.whiskeringRight ℕᵒᵖ B' B).obj s ≅
      (Functor.whiskeringRight ℕᵒᵖ A' A).obj r ⋙
        (Functor.whiskeringRight ℕᵒᵖ A B).obj F)
    (hd : ∀ T n, (d.hom.app T).app n = c.hom.app (T.obj n))
    (T : ℕᵒᵖ ⥤ A') :
    s.map (limit.post T F') ≫ limit.post (T ⋙ F') s ≫ lim.map (d.hom.app T) =
      c.hom.app (limit T) ≫ F.map (limit.post T r) ≫ limit.post (T ⋙ r) F := by
  apply limit.hom_ext
  intro n
  simp only [Category.assoc, lim_map, limMap_π, limit.post_π_assoc,
    ← s.map_comp_assoc, limit.post_π, hd]
  change s.map (F'.map (limit.π T n)) ≫ c.hom.app (T.obj n) =
    c.hom.app (limit T) ≫ F.map (limit.post T r) ≫
      limit.post (T ⋙ r) F ≫ limit.π ((T ⋙ r) ⋙ F) n
  rw [limit.post_π, ← F.map_comp, limit.post_π]
  exact c.hom.naturality (limit.π T n)

-- The normalization fields have an abstract categorical API. Keeping the diagram
-- chase at this level avoids repeatedly unfolding the sheaf and chosen-limit data.
-- The normalization chase retains arbitrary localization universes and all unit factors.
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}

-- Elaborate the comparison interfaces and the two scalar-restriction adjunctions.
end CategoryTheory.FlatScalarTowerLimit
