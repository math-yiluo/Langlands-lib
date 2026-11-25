/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import WeilConjectures.CategoryTheory.SectionProjectionUnit
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Base change for the ordered tensor trace evaluation

Source: blueprint thm-amb-p1-adjunction.proof.md, the counit base-change square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance 40000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] Abelian.toPreadditive
attribute [local instance 21000] sheafBraidedCategory
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  upperStar
  leftDerivedUpperStarCompSectionIso

variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]

omit [UpperStarPreservesFlat B] in
/-- Identity inverse image has the identity tensor comparison under its canonical
identity comparison. -/
private theorem identityPullback_tensor (X : Scheme.{u})
    (M N : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    ((canonicalPullbackTensorComparison B (𝟙 X)).app M).app N ≫
        ((leftDerivedUpperStarId B X).hom.app M ⊗ₘ
          (leftDerivedUpperStarId B X).hom.app N) =
      (leftDerivedUpperStarId B X).hom.app (M ⊗ N) := by
  exact Adjunction.tensor_compatibility_of_unit_law
    (C := DerivedCategory (Sheaf X.smallEtaleTopology B))
    ((upperStar B (𝟙 X)).leftDerivedFunctor)
    (canonicalPullbackTensorComparison B (𝟙 X))
    (leftDerivedUpperStarComp B (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp _).symm)
    (leftDerivedUpperStarId B X)
    (fun M N ↦ by
      simpa only [canonicalPullbackTensorComparison_eq] using
        leftDerivedUpperStarTensorComparison_comp B (𝟙 X) (𝟙 X)
          (𝟙 X) (Category.id_comp _).symm M N)
    (fun M ↦ leftDerivedUpperStarComp_id_right_hom_app B (𝟙 X) M) M N

/-- Pullback along a section is tensor compatible with its identity comparison. -/
theorem sectionPullback_tensor {X Y : Scheme.{u}}
    (s : Y ⟶ X) (p : X ⟶ Y) (h : s ≫ p = 𝟙 Y)
    (M N : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (upperStar B s).leftDerivedFunctor.map
        (((canonicalPullbackTensorComparison B p).app M).app N) ≫
      ((canonicalPullbackTensorComparison B s).app
        ((upperStar B p).leftDerivedFunctor.obj M)).app
          ((upperStar B p).leftDerivedFunctor.obj N) ≫
      ((leftDerivedUpperStarCompSectionIso B s p h).hom.app M ⊗ₘ
        (leftDerivedUpperStarCompSectionIso B s p h).hom.app N) =
      (leftDerivedUpperStarCompSectionIso B s p h).hom.app (M ⊗ N) := by
  have hc := leftDerivedUpperStarTensorComparison_comp B s p (𝟙 Y) h.symm M N
  simp only [← canonicalPullbackTensorComparison_eq] at hc
  apply (cancel_epi ((leftDerivedUpperStarComp B s p (𝟙 Y) h.symm).hom.app
    (M ⊗ N))).mp
  simp only [leftDerivedUpperStarCompSectionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [← reassoc_of% hc, tensorHom_comp_tensorHom,
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]
  exact identityPullback_tensor B Y M N

attribute [local instance] DerivedCategory.symmetricCategory'
attribute [local instance 20000] derivedBraidedCategory

/-- The ordered projection is the projection for the flipped tensor comparison. -/
theorem orderedProjection_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (((derivedUpperStarLowerStarAdjunction B f).rightAdjointProjectionMap
      (T_C := (derivedTensor B X).flip) (T_D := (derivedTensor B Y).flip)
      ((flipFunctor _ _ _).map (canonicalPullbackTensorComparison B f))).app E).app K =
      (β_ K ((lowerStar B f).rightDerivedFunctor.obj E)).hom ≫
        ((rightDerivedLowerStarProjectionMap B f).app E).app K ≫
        (lowerStar B f).rightDerivedFunctor.map
          (β_ E ((upperStar B f).leftDerivedFunctor.obj K)).hom := by
  unfold canonicalPullbackTensorComparison
  exact Adjunction.rightAdjointProjectionMap_flip
    (derivedUpperStarLowerStarAdjunction B f) (leftDerivedUpperStarTensorComparison B f)
    (fun P Q ↦ by
      exact leftDerivedUpperStar_map_braiding_hom_δ B f P Q) E K

/-- A scalar supported integral along a proper section contracts arbitrary tensors. -/
theorem etaleSectionIntegralTensor
    {X Y : Scheme.{u}} (s : X ⟶ Y) (p : Y ⟶ X) (h : s ≫ p = 𝟙 X)
    (M U : DerivedCategory (Sheaf X.smallEtaleTopology B)) (e : U ≅ 𝟙_ _)
    (V : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (δ : (lowerStar B s).rightDerivedFunctor.obj U ⟶ V)
    (τ : (lowerStar B p).rightDerivedFunctor.obj V ⟶ U) :
    let F := (upperStar B p).leftDerivedFunctor
    let R := (lowerStar B p).rightDerivedFunctor
    let S := (lowerStar B s).rightDerivedFunctor
    let l := leftDerivedUpperStarCompSectionIso B s p h
    let t := conjugateIsoEquiv
      ((derivedUpperStarLowerStarAdjunction B p).comp
        (derivedUpperStarLowerStarAdjunction B s)) Adjunction.id l.symm
    let pF := (derivedUpperStarLowerStarAdjunction B p).rightAdjointProjectionMap
      (T_C := (derivedTensor B Y).flip) (T_D := (derivedTensor B X).flip)
      ((flipFunctor
        (DerivedCategory (Sheaf X.smallEtaleTopology B))
        (DerivedCategory (Sheaf X.smallEtaleTopology B))
        (DerivedCategory (Sheaf Y.smallEtaleTopology B))).map
        (canonicalPullbackTensorComparison B p))
    let pG := (derivedUpperStarLowerStarAdjunction B s).rightAdjointProjectionMap
      (T_C := (derivedTensor B X).flip) (T_D := (derivedTensor B Y).flip)
      ((flipFunctor
        (DerivedCategory (Sheaf Y.smallEtaleTopology B))
        (DerivedCategory (Sheaf Y.smallEtaleTopology B))
        (DerivedCategory (Sheaf X.smallEtaleTopology B))).map
        (canonicalPullbackTensorComparison B s))
    let q := (pG.app U).app (F.obj M) ≫
      S.map (((derivedTensor B X).map (l.hom.app M)).app U ≫
        ((derivedTensor B X).obj M).map e.hom ≫ (derivedTensorRightUnitor B X M).hom)
    ∀ [IsIso ((pF.app (S.obj U)).app M)] [IsIso ((pF.app V).app M)] [IsIso q],
    (t.inv.app U ≫ R.map δ ≫ τ = 𝟙 U) →
    t.inv.app M ≫ R.map (inv q) ≫ R.map (((derivedTensor B Y).obj (F.obj M)).map δ) ≫
      inv ((pF.app V).app M) ≫ ((derivedTensor B X).obj M).map τ ≫
      ((derivedTensor B X).obj M).map e.hom ≫ (derivedTensorRightUnitor B X M).hom = 𝟙 M := by
  intro F R S l t pF pG q hp hpV hq hδ
  apply Adjunction.section_integral_tensor_iso t M U e V
    ((pF.app (S.obj U)).app M) ((pF.app V).app M) q δ τ
  · exact NatTrans.congr_app (pF.naturality δ) M |>.symm
  · exact hδ
  · exact Adjunction.section_projection_inverse_iso R t M U e _ _ q
      (Adjunction.section_projection_unit_iso
        (derivedUpperStarLowerStarAdjunction B p)
        (derivedUpperStarLowerStarAdjunction B s)
        (canonicalPullbackTensorComparison B p)
        (canonicalPullbackTensorComparison B s) l M U e
        (sectionPullback_tensor B s p h M U))

/-- The canonical square of ordered projections and proper exchange. -/
private theorem orderedProjection_baseChange
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    let p := (derivedUpperStarLowerStarAdjunction B f).rightAdjointProjectionMap
      (T_C := (derivedTensor B X).flip) (T_D := (derivedTensor B Y).flip)
      ((flipFunctor _ _ _).map (canonicalPullbackTensorComparison B f))
    let p' := (derivedUpperStarLowerStarAdjunction B f').rightAdjointProjectionMap
      (T_C := (derivedTensor B X').flip) (T_D := (derivedTensor B Y').flip)
      ((flipFunctor _ _ _).map (canonicalPullbackTensorComparison B f'))
    (upperStar B g).leftDerivedFunctor.map ((p.app E).app K) ≫
        (derivedBaseChangeMap B sq).app
          (((upperStar B f).leftDerivedFunctor.obj K) ⊗ E) ≫
        (lowerStar B f').rightDerivedFunctor.map
          (((canonicalPullbackTensorComparison B g').app
            ((upperStar B f).leftDerivedFunctor.obj K)).app E) =
      ((canonicalPullbackTensorComparison B g).app K).app
          ((lowerStar B f).rightDerivedFunctor.obj E) ≫
        (upperStar B g).leftDerivedFunctor.obj K ◁ (derivedBaseChangeMap B sq).app E ≫
        (p'.app ((upperStar B g').leftDerivedFunctor.obj E)).app
          ((upperStar B g).leftDerivedFunctor.obj K) ≫
        (lowerStar B f').rightDerivedFunctor.map
          ((derivedSquareUpperStarIso B sq).hom.app K ▷
            (upperStar B g').leftDerivedFunctor.obj E) := by
  exact Adjunction.rightAdjointProjectionMap_mate
    (T₁ := (curriedTensor (DerivedCategory (Sheaf X.smallEtaleTopology B))).flip)
    (S₁ := (curriedTensor (DerivedCategory (Sheaf Y.smallEtaleTopology B))).flip)
    (T₂ := (curriedTensor (DerivedCategory (Sheaf X'.smallEtaleTopology B))).flip)
    (S₂ := (curriedTensor (DerivedCategory (Sheaf Y'.smallEtaleTopology B))).flip)
    (derivedUpperStarLowerStarAdjunction B f)
    (derivedUpperStarLowerStarAdjunction B f')
    ((flipFunctor _ _ _).map (canonicalPullbackTensorComparison B f))
    ((flipFunctor _ _ _).map (canonicalPullbackTensorComparison B f'))
    ((flipFunctor _ _ _).map (canonicalPullbackTensorComparison B g))
    ((flipFunctor _ _ _).map (canonicalPullbackTensorComparison B g'))
    (derivedSquareUpperStarIso B sq).hom (derivedBaseChangeMap B sq)
    (fun a b ↦ by
      simpa only [tensorHom_def', flipFunctor_map_app_app, Functor.flip_obj_obj,
        Functor.flip_map_app,
        Functor.flip_obj_map, curriedTensor_obj_obj, curriedTensor_map_app,
        curriedTensor_obj_map, canonicalPullbackTensorComparison_eq] using
        derivedSquareUpperStarIso_hom_tensor B sq b a)
    (derivedUpperStar_map_derivedBaseChangeMap_app_counit B sq) E K

/-- Tensoring a scalar trace square with an arbitrary complex gives the evaluation square.
Source: blueprint thm-amb-p1-adjunction.proof.md, final base-change calculation.
Proof: the mate projection square is tensor compatible by the pullback composition
coherence. Cancel the ordered projection, use naturality with respect to the scalar
trace square, and finish with the pullback right-unit law. -/
theorem etaleTensorEvaluation_constant_baseChange
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (L' : DerivedCategory (Sheaf X'.smallEtaleTopology B))
    (c : (upperStar B g').leftDerivedFunctor.obj L ≅ L')
    (O : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (O' : DerivedCategory (Sheaf Y'.smallEtaleTopology B))
    (cO : (upperStar B g).leftDerivedFunctor.obj O ⟶ O')
    (r : ∀ K : DerivedCategory (Sheaf Y.smallEtaleTopology B),
      ((derivedTensor B Y).obj K).obj O ≅ K)
    (r' : ∀ K : DerivedCategory (Sheaf Y'.smallEtaleTopology B),
      ((derivedTensor B Y').obj K).obj O' ≅ K)
    (τ : (lowerStar B f).rightDerivedFunctor.obj L ⟶ O)
    (τ' : (lowerStar B f').rightDerivedFunctor.obj L' ⟶ O')
    (ht : (upperStar B g).leftDerivedFunctor.map τ ≫
        cO =
      (derivedBaseChangeMap B sq).app L ≫
        (lowerStar B f').rightDerivedFunctor.map c.hom ≫ τ')
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (hu : ((canonicalPullbackTensorComparison B g).app K).app O ≫
        ((derivedTensor B Y').obj ((upperStar B g).leftDerivedFunctor.obj K)).map cO ≫
          (r' ((upperStar B g).leftDerivedFunctor.obj K)).hom =
      (upperStar B g).leftDerivedFunctor.map (r K).hom) :
    let p := (derivedUpperStarLowerStarAdjunction B f).rightAdjointProjectionMap
      (T_C := (derivedTensor B X).flip) (T_D := (derivedTensor B Y).flip)
      ((flipFunctor _ _ _).map (canonicalPullbackTensorComparison B f))
    let p' := (derivedUpperStarLowerStarAdjunction B f').rightAdjointProjectionMap
      (T_C := (derivedTensor B X').flip) (T_D := (derivedTensor B Y').flip)
      ((flipFunctor _ _ _).map (canonicalPullbackTensorComparison B f'))
    ∀ (π : ((derivedTensor B Y).obj K).obj
        ((lowerStar B f).rightDerivedFunctor.obj L) ⟶
      (lowerStar B f).rightDerivedFunctor.obj
        (((derivedTensor B X).obj ((upperStar B f).leftDerivedFunctor.obj K)).obj L))
      (π' : ((derivedTensor B Y').obj ((upperStar B g).leftDerivedFunctor.obj K)).obj
        ((lowerStar B f').rightDerivedFunctor.obj L') ⟶
        (lowerStar B f').rightDerivedFunctor.obj
          (((derivedTensor B X').obj ((upperStar B f').leftDerivedFunctor.obj
            ((upperStar B g).leftDerivedFunctor.obj K))).obj L')),
    π = (p.app L).app K →
    π' = (p'.app L').app ((upperStar B g).leftDerivedFunctor.obj K) →
    ∀ [IsIso π] [IsIso π'],
    (upperStar B g).leftDerivedFunctor.map
        (inv π ≫ ((derivedTensor B Y).obj K).map τ ≫ (r K).hom) =
      (derivedBaseChangeMap B sq).app
          (((derivedTensor B X).obj ((upperStar B f).leftDerivedFunctor.obj K)).obj L) ≫
        (lowerStar B f').rightDerivedFunctor.map
          (((canonicalPullbackTensorComparison B g').app
            ((upperStar B f).leftDerivedFunctor.obj K)).app L ≫
            (derivedTensorHom B ((derivedSquareUpperStarIso B sq).inv.app K) c.hom)) ≫
        inv π' ≫
        ((derivedTensor B Y').obj ((upperStar B g).leftDerivedFunctor.obj K)).map τ' ≫
          (r' ((upperStar B g).leftDerivedFunctor.obj K)).hom := by
  intro p p' π π' hπ hπ' hp hp'
  subst π
  subst π'
  exact Adjunction.tensor_evaluation_baseChange_constant
    ((upperStar B f).leftDerivedFunctor) ((lowerStar B f).rightDerivedFunctor)
    ((upperStar B f').leftDerivedFunctor) ((lowerStar B f').rightDerivedFunctor)
    ((upperStar B g).leftDerivedFunctor) ((upperStar B g').leftDerivedFunctor)
    (derivedSquareUpperStarIso B sq) (derivedBaseChangeMap B sq) p p'
    (canonicalPullbackTensorComparison B g) (canonicalPullbackTensorComparison B g')
    O O' cO r r' L L' c τ τ' ht K
    (orderedProjection_baseChange B sq L K)
    hu

end AlgebraicGeometry.Etale
