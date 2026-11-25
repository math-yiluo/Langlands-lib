/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data

/-!
# The counit defined by an ordinary finite trace

Source: blueprint lemma-cohomology-projective-line-trace, the displayed inverse-projection formula.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local irreducible] derivedTensor singleFunctorObjUnitIso

/-- Naturality of the ordered projection in its base coefficient.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node).
Proof: compose naturality of the two tensor symmetries with naturality of the
adjoint-of-counit projection. Direct image preserves the resulting composition. -/
theorem ordinaryFiniteProjection_naturality
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (q : X ⟶ Y)
    (L : DerivedCategoryModule A X) {K K' : DerivedCategoryModule A Y} (f : K ⟶ K') :
    ((ordinaryFiniteTensor A Y).map f).app ((ordinaryFinitePushforward A q).obj L) ≫
        ordinaryFiniteProjection A q L K' =
      ordinaryFiniteProjection A q L K ≫
        (ordinaryFinitePushforward A q).map
          (((ordinaryFiniteTensor A X).map ((ordinaryFinitePullback A q).map f)).app L) := by
  have hs := NatTrans.congr_app
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.naturality f)
    ((ordinaryFinitePushforward A q).obj L)
  have hp := ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app L).naturality f
  have ht := ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app L).naturality
    ((ordinaryFinitePullback A q).map f)
  dsimp only [Functor.flip_obj_map, Functor.flip_map_app, NatTrans.comp_app,
    Functor.comp_map] at hs ht
  change ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((ordinaryFinitePushforward A q).obj L)).map f ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app L).app K' =
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app L).app K ≫
        (ordinaryFinitePushforward A q).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj L).map
            ((ordinaryFinitePullback A q).map f)) at hp
  dsimp only [ordinaryFiniteProjection, ordinaryFiniteTensor]
  rw [← Category.assoc, hs, Category.assoc, ← Category.assoc _ _
    ((ordinaryFinitePushforward A q).map _), hp]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun g ↦
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).app _ ≫
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app L).app K ≫
        (ordinaryFinitePushforward A q).map g) ht

/-- The ordered proper projection, natural in the base coefficient.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node). -/
def ordinaryFiniteProjectionNatTrans
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (q : X ⟶ Y)
    (L : DerivedCategoryModule A X) :
    derivedTensorRight (ModuleCat.{u + 1} A) Y
        ((ordinaryFinitePushforward A q).obj L) ⟶
      ordinaryFiniteTwistedPullback A q L ⋙ ordinaryFinitePushforward A q where
  app K := ordinaryFiniteProjection A q L K
  naturality := fun {_ _} f ↦ ordinaryFiniteProjection_naturality A q L f

/-- The right tensor unitor, formed with the same derived monoidal structure as tensor.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node). -/
def ordinaryDerivedTensorRightUnitorNatIso
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] (Y : Scheme.{u}) :
    derivedTensorRight C Y (𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology C))) ≅
      𝟭 (DerivedCategory (Sheaf Y.smallEtaleTopology C)) :=
  by
    unfold derivedTensorRight derivedTensor
    exact rightUnitorNatIso _

/-- Tensoring a morphism to the constant unit, followed by the right unitor.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node). -/
def ordinaryDerivedTensorTrace
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] (Y : Scheme.{u})
    {B : DerivedCategory (Sheaf Y.smallEtaleTopology C)}
    (τ : B ⟶ (DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf Y.smallEtaleTopology C).obj (𝟙_ C))) :
    derivedTensorRight C Y B ⟶ 𝟭 (DerivedCategory (Sheaf Y.smallEtaleTopology C)) :=
  (derivedTensorRightFunctor C Y).map (τ ≫ (singleFunctorObjUnitIso C Y).hom) ≫
    (ordinaryDerivedTensorRightUnitorNatIso C Y).hom

/-- Tensoring a finite-coefficient trace, followed by the tensor unit.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node). -/
def ordinaryFiniteTensorTrace (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    {B : DerivedCategoryModule A Y} (τ : B ⟶ ordinaryFiniteUnit A Y) :
    derivedTensorRight (ModuleCat.{u + 1} A) Y B ⟶ 𝟭 (DerivedCategoryModule A Y) :=
  ordinaryDerivedTensorTrace (ModuleCat.{u + 1} A) Y τ

/-- The tensor-trace component is exactly tensor with the trace and the prescribed unitor.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node).
Proof: expand the natural transformation and use preservation of composition by tensor. -/
theorem ordinaryFiniteTensorTrace_app (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    {B : DerivedCategoryModule A Y} (τ : B ⟶ ordinaryFiniteUnit A Y)
    (K : DerivedCategoryModule A Y) :
    (ordinaryFiniteTensorTrace A Y τ).app K =
      ((ordinaryFiniteTensor A Y).obj K).map τ ≫ (derivedTensorSingleUnitIso K).hom := by
  change ((ordinaryFiniteTensor A Y).obj K).map
      (τ ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom) ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom = _
  rw [Functor.map_comp, Category.assoc]
  rfl

/-- The inverse ordered proper projection followed by the tensor trace, on all complexes.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteTraceCounit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    [IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian Y] [CompactSpace Y]
    (L : DerivedCategoryModule A X)
    (τ : (ordinaryFinitePushforward A q).obj L ⟶ ordinaryFiniteUnit A Y) :
    ordinaryFiniteTwistedPullback A q L ⋙ ordinaryFinitePushforward A q ⟶
      𝟭 (DerivedCategoryModule A Y) :=
  letI : IsIso (ordinaryFiniteProjectionNatTrans A q L) :=
    letI (K : DerivedCategoryModule A Y) :
        IsIso ((ordinaryFiniteProjectionNatTrans A q L).app K) :=
      isIso_proper_projection_formula_reordered A q L K
    NatIso.isIso_of_isIso_app _
  inv (ordinaryFiniteProjectionNatTrans A q L) ≫ ordinaryFiniteTensorTrace A Y τ

/-- The trace counit satisfies the actual ordered projection equation.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node).
Proof: cancel the ordered projection with its inverse and apply the tensor-trace formula. -/
theorem ordinaryFiniteTraceCounit_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    [IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian Y] [CompactSpace Y]
    (L : DerivedCategoryModule A X)
    (τ : (ordinaryFinitePushforward A q).obj L ⟶ ordinaryFiniteUnit A Y)
    (K : DerivedCategoryModule A Y) :
    ordinaryFiniteProjection A q L K ≫ (ordinaryFiniteTraceCounit A q L τ).app K =
      ((ordinaryFiniteTensor A Y).obj K).map τ ≫ (derivedTensorSingleUnitIso K).hom := by
  unfold ordinaryFiniteTraceCounit
  have : IsIso (ordinaryFiniteProjectionNatTrans A q L) :=
    letI (K : DerivedCategoryModule A Y) :
        IsIso ((ordinaryFiniteProjectionNatTrans A q L).app K) :=
      isIso_proper_projection_formula_reordered A q L K
    NatIso.isIso_of_isIso_app _
  change (ordinaryFiniteProjectionNatTrans A q L).app K ≫
    ((inv (ordinaryFiniteProjectionNatTrans A q L)).app K ≫ _) = _
  rw [← Category.assoc, ← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app,
    Category.id_comp, ordinaryFiniteTensorTrace_app]

/-- The canonical natural counit obtained from a projective-line splitting.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteP1TraceCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (b : ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) :
    ordinaryFiniteP1Right A N hA S ⋙ ordinaryFinitePushforward A (ProjectiveLine S ↘ S) ⟶
      𝟭 (DerivedCategoryModule A S) :=
  letI : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  letI : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  ordinaryFiniteTraceCounit A (ProjectiveLine S ↘ S)
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) (b.inv ≫ biprod.snd)

/-- The projective-line counit uses exactly the item's ordered projection and unitor.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node).
Proof: apply the general inverse-projection equation to q, its shifted line, and the trace. -/
theorem ordinaryFiniteP1TraceCounit_projection (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (b : ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
    (K : DerivedCategoryModule A S) :
    ordinaryFiniteProjection A (ProjectiveLine S ↘ S)
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K ≫
      (ordinaryFiniteP1TraceCounit A N hA S b).app K =
    ((ordinaryFiniteTensor A S).obj K).map (b.inv ≫ biprod.snd) ≫
      (derivedTensorSingleUnitIso K).hom := by
  unfold ordinaryFiniteP1TraceCounit
  have : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  have : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  exact ordinaryFiniteTraceCounit_projection A (ProjectiveLine S ↘ S)
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) (b.inv ≫ biprod.snd) K

end AlgebraicGeometry.Etale
