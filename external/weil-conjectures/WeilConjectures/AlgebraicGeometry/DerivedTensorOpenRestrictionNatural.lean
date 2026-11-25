/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.KFlatBifunctorIsoDescent
import WeilConjectures.AlgebraicGeometry.OpenRestrictionKFlatModel
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Natural tensor comparison for derived open restriction

Source: Stacks Project, Tag 06YH (derived tensor construction) and Tag 08EU (locality).
(blueprint: lem-pc-derived-tensor-open-restriction-natural).
-/

@[expose] public section

universe u w wO
open CategoryTheory MonoidalCategory
set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace AlgebraicGeometry

private noncomputable local instance restrictionNaturalModuleTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

private local instance restrictionNaturalModuleGrothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)


-- Compose model comparisons abstractly to avoid unfolding concrete localization functors.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def tensorModelComposition
    {I C D E H : Type*} [Category I] [Category C] [Category D]
    [Category E] [Category H] [MonoidalCategory E] [MonoidalCategory H]
    (F : I ⥤ C) (Q : C ⥤ E) (Q' : D ⥤ H) (RC : C ⥤ D) (RD : E ⥤ H)
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (a : curriedTensorPre (F ⋙ Q) ≅
      (Functor.postcompose₂.obj Q).obj
        (((Functor.whiskeringLeft₂ C).obj F).obj F |>.obj T))
    (c : curriedTensorPre (F ⋙ RC ⋙ Q') ≅
      (Functor.postcompose₂.obj Q').obj
        (((Functor.whiskeringLeft₂ D).obj (F ⋙ RC)).obj (F ⋙ RC) |>.obj T'))
    (b : (Functor.postcompose₂.obj RC).obj T ≅
      (((Functor.whiskeringLeft₂ D).obj RC).obj RC).obj T')
    (d : Q ⋙ RD ≅ RC ⋙ Q') :
    (((Functor.whiskeringLeft₂ H).obj (F ⋙ Q)).obj (F ⋙ Q)).obj
        (curriedTensorPost RD) ≅
      (((Functor.whiskeringLeft₂ H).obj (F ⋙ Q)).obj (F ⋙ Q)).obj
        (curriedTensorPre RD) := by
  let TF := (((Functor.whiskeringLeft₂ C).obj F).obj F).obj T
  exact (Functor.postcompose₂.obj RD).mapIso a ≪≫
    (Functor.postcompose₂.mapIso d).app TF ≪≫
    (((Functor.whiskeringLeft₂ H).obj F).obj F).mapIso
      ((Functor.postcompose₂.obj Q').mapIso b) ≪≫ c.symm ≪≫
    (curriedTensorPreFunctor.mapIso (Functor.isoWhiskerLeft F d)).symm

private theorem bifunctorModelNaturality
    {I D E : Type*} [Category I] [Category D] [Category E]
    (V W : D ⥤ D ⥤ E) (J : I ⥤ D)
    (α : (((Functor.whiskeringLeft₂ E).obj J).obj J).obj V ≅
      (((Functor.whiskeringLeft₂ E).obj J).obj J).obj W)
    {P P' N N' : I} (f : P ⟶ P') (g : N ⟶ N') :
    (V.map (J.map f)).app (J.obj N) ≫ (V.obj (J.obj P')).map (J.map g) ≫
      ((α.app P').app N').hom =
    ((α.app P).app N).hom ≫ (W.map (J.map f)).app (J.obj N) ≫
      (W.obj (J.obj P')).map (J.map g) := by
  have h₁ := congr_app (α.hom.naturality f) N
  have h₂ := (α.hom.app P').naturality g
  change (V.map (J.map f)).app (J.obj N) ≫ ((α.app P').app N).hom =
    ((α.app P).app N).hom ≫ (W.map (J.map f)).app (J.obj N) at h₁
  change (V.obj (J.obj P')).map (J.map g) ≫ ((α.app P').app N').hom =
    ((α.app P').app N).hom ≫ (W.obj (J.obj P')).map (J.map g) at h₂
  rw [h₂, ← Category.assoc, h₁, Category.assoc]

private def tensorRestrictionIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (R : C ⥤ D) (μ : curriedTensorPost R ≅ curriedTensorPre R) :
    tensor C ⋙ R ≅ R.prod R ⋙ tensor D := by
  refine NatIso.ofComponents (fun P ↦ (μ.app P.1).app P.2) ?_
  intro P P' f
  have h₁ := congr_app (μ.hom.naturality f.1) P.2
  have h₂ := (μ.hom.app P'.1).naturality f.2
  change R.map (f.1 ▷ P.2) ≫ ((μ.app P'.1).app P.2).hom =
    ((μ.app P.1).app P.2).hom ≫ R.map f.1 ▷ R.obj P.2 at h₁
  change R.map (P'.1 ◁ f.2) ≫ ((μ.app P'.1).app P'.2).hom =
    ((μ.app P'.1).app P.2).hom ≫ R.obj P'.1 ◁ R.map f.2 at h₂
  change R.map (f.1 ⊗ₘ f.2) ≫ ((μ.app P'.1).app P'.2).hom =
    ((μ.app P.1).app P.2).hom ≫ (R.map f.1 ⊗ₘ R.map f.2)
  rw [tensorHom_def, Functor.map_comp, Category.assoc, h₂,
    ← Category.assoc, h₁, Category.assoc]
  rw [tensorHom_def]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Matching total-tensor and localization bifunctors needs additional reduction heartbeats.
/-- Exact open restriction commutes naturally with the derived tensor bifunctor.
Source: Stacks Project, Tag 06YH (derived tensor construction) and Tag 08EU, locality.
Proof: use the full category of K-flat models for both tensor inputs. Every
complex admits a K-flat resolution, and exact open restriction preserves
K-flatness. The natural sheaf tensor restriction comparison,
and commutation of restriction with the coproducts defining totalization, identify
restriction of the total tensor with the total tensor of restrictions. The K-flat
comparison identifies these models with the chosen derived tensors. Naturality in
complex maps and invariance under quasi-isomorphisms descend the comparison and its
inverse through the product derived localization. K-flat resolutions of common
refinements of quasi-isomorphism roofs show that the result is independent of the
models and natural in arbitrary derived morphisms. Transport by the derived-category
comparison equivalences accommodates independent universes. The comparison and its
inverse satisfy the two identity equations already on total tensor models, hence
also after localization. This construction applies to the empty open as well.
(blueprint: lem-pc-derived-tensor-open-restriction-natural). -/
theorem derivedTensor_openRestriction_natIso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wO} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    let R := (schemeOpenRestriction X U).mapDerivedCategory
    Nonempty (tensor (schemeDerivedCategory X) ⋙ R ≅
      R.prod R ⋙ tensor (schemeDerivedCategory U.toScheme)) := by
  classical
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  have : Limits.HasColimitsOfSize.{0, 0} A := Limits.hasColimitsOfSizeShrink.{0, 0, u, u} A
  have : Limits.HasColimitsOfSize.{0, 0} B := Limits.hasColimitsOfSizeShrink.{0, 0, u, u} B
  let R := schemeOpenRestriction X U
  let i := Scheme.Modules.overFunctorEquiv U ≪≫
    Scheme.Modules.restrictFunctorIsoPullback U.ι
  let : (Scheme.Modules.pullback U.ι).Monoidal := Scheme.Modules.pullbackMonoidal U.ι
  let : R.Monoidal := Functor.Monoidal.transport i.symm
  have : Limits.PreservesColimitsOfSize.{0, 0} R := by
    dsimp [R, schemeOpenRestriction, SheafOfModules.overFunctor]
    infer_instance
  let RC := R.mapHomologicalComplex (.up ℤ)
  let RD := R.mapDerivedCategory
  let QX := DerivedCategory.Q (C := A)
  let QU := DerivedCategory.Q (C := B)
  let K : ObjectProperty (CochainComplex A ℤ) :=
    fun P ↦ CochainComplex.IsKFlatTensor (R := X.sheaf) P
  let F := K.ι
  obtain ⟨a⟩ := kFlat_derivedTensor_comparison_natIso X F F (fun P ↦ P.property)
  obtain ⟨c⟩ := kFlat_derivedTensor_comparison_natIso U.toScheme (F ⋙ RC) (F ⋙ RC)
    (fun P ↦ openRestriction_isKFlat X U P.obj P.property)
  let b := asIso (HomologicalComplex.mapBifunctorComparisonNatTrans
    (c₁ := .up ℤ) (c₂ := .up ℤ) (Functor.OplaxMonoidal.δNatTrans R) (.up ℤ))
  let d := R.mapDerivedCategoryFactors
  let V := curriedTensorPost RD
  let W := curriedTensorPre RD
  let J := F ⋙ QX
  let pre := ((Functor.whiskeringLeft₂ (schemeDerivedCategory U.toScheme)).obj J).obj J
  let α : pre.obj V ≅ pre.obj W := tensorModelComposition F QX QU RC RD
    (curriedTensor A).map₂CochainComplex (curriedTensor B).map₂CochainComplex a c b d
  obtain ⟨μ, _⟩ := kFlat_bifunctor_iso_descent X V W
    (fun P N hP hN ↦ (α.app ⟨P, hP⟩).app ⟨N, hN⟩) (by
      intro P P' N N' hP hP' hN hN' f g
      exact bifunctorModelNaturality V W J α
        (ObjectProperty.homMk (X := ⟨P, hP⟩) (Y := ⟨P', hP'⟩) f)
        (ObjectProperty.homMk (X := ⟨N, hN⟩) (Y := ⟨N', hN'⟩) g))
  exact ⟨tensorRestrictionIso RD μ⟩

end AlgebraicGeometry
