/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalScalarTensorPullModels
import all WeilConjectures.AlgebraicGeometry.IntegralResidueScalarCounitModel
import WeilConjectures.AlgebraicGeometry.InternalScalarOrdinaryTensorPullModel
import WeilConjectures.AlgebraicGeometry.InternalScalarPullTensorCounit
import all WeilConjectures.AlgebraicGeometry.InternalScalarRestrictionMateNormalization

/-! # The scalar route in the common tensor model

Source: Stacks 06YY, 0G7E, 07A6; integral proper-base-change proof (1), (3).
(auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.QuotientChange
set_option allowUnsafeReducibility true
attribute [local reducible] D
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

private theorem scalar_restriction_counit (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (hlam : PullNormalized a f lam)
    (P : HomotopyCategory (Modules Λ Y) (.up ℤ)) :
    let FP := ((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ)).obj P
    let TP := ((extension a Y).mapHomotopyCategory (.up ℤ)).obj P
    let ph := (NatTrans.mapHomotopyCategory (CondensedRing.pullIso a f).inv (.up ℤ)).app P
    let qh := (NatTrans.mapHomotopyCategory
      (CondensedRing.comapUpperStarIso a f).inv (.up ℤ)).app TP
    (scalarTensorRestrictPullIso a f).hom.app ((D a Y).obj (DerivedCategory.Qh.obj P)) ≫
      (V a X).map (lam.hom.app (DerivedCategory.Qh.obj P)) ≫
      (V a X).map ((D a X).map ((pullCounit (Λ := Λ) f).app P)) ≫
      (V a X).map ((scalarCounit a X).app FP) ≫
      (V₀ a X).mapDerivedCategoryFactorsh.hom.app
        (((extension a X).mapHomotopyCategory (.up ℤ)).obj FP) =
    (L Λ f).map ((V a Y).map ((scalarCounit a Y).app P) ≫
      (V₀ a Y).mapDerivedCategoryFactorsh.hom.app TP) ≫
      (pullCounit (Λ := Λ) f).app (((V₀ a Y).mapHomotopyCategory (.up ℤ)).obj TP) ≫
      DerivedCategory.Qh.map (qh ≫ ((V₀ a X).mapHomotopyCategory (.up ℤ)).map ph) := by
  dsimp only
  have hmi := hlam P
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app, map_comp_iso_eq,
    Iso.symm_hom] at hmi
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at hmi
  have ho := (V₀ a X).mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory (CondensedRing.pullIso a f).inv (.up ℤ)).app P)
  have hq := restriction_pull_fac a f
    (((extension a Y).mapHomotopyCategory (.up ℤ)).obj P)
  change (scalarTensorRestrictPullIso a f).hom.app _ ≫ _ ≫ _ = _ at hq
  have hn := (scalarTensorRestrictPullIso a f).hom.naturality
    ((scalarCounit a Y).app P)
  dsimp only [Functor.comp_map] at hn ho
  simp only [← Functor.map_comp_assoc]
  rw [hmi]
  simp only [Functor.map_comp, Category.assoc]
  erw [ho]
  erw [← reassoc_of% hn]
  erw [reassoc_of% hq]

-- Compose the counit and tensor squares before specializing the diagram to sheaves.
private theorem scalar_route_pasting
    {C E H K : Type*} [Category C] [Category E] [Category H] [Category K]
    (F : C ⥤ E) (QY : H ⥤ C) (FH : H ⥤ K) (QX : K ⥤ E)
    (α : QY ⋙ F ⟶ FH ⋙ QX)
    {N N' : C} {U V W : H} {A Z : K} {J M R R' T : E}
    (q : F.obj N ⟶ J) (a : J ⟶ M) (t : M ⟶ T) (target : T ⟶ QX.obj Z)
    (b : M ⟶ R) (gX : R ⟶ R') (kX : R' ⟶ QX.obj A)
    (gY : N ⟶ N') (kY : N' ⟶ QY.obj U) (εY : N ⟶ QY.obj V)
    (r : FH.obj U ⟶ A) (sX : A ⟶ Z)
    (tY : U ⟶ V) (sY : V ⟶ W) (δ : FH.obj W ⟶ Z)
    (ht : t ≫ target = b ≫ gX ≫ kX ≫ QX.map sX)
    (hY : εY = gY ≫ kY ≫ QY.map tY)
    (h : q ≫ a ≫ b ≫ gX ≫ kX = F.map (gY ≫ kY) ≫ α.app U ≫ QX.map r)
    (ho : r ≫ sX = FH.map (tY ≫ sY) ≫ δ) :
    q ≫ a ≫ t ≫ target = F.map εY ≫ α.app V ≫ QX.map (FH.map sY ≫ δ) := by
  rw [ht, hY]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h]
  simp only [← QX.map_comp]
  rw [ho]
  have hn := α.naturality tY
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]

-- The counit calculation contains several nested derived functor comparisons.
/-- The scalar route computes the ordinary balanced pullback map.

Source: Stacks 06YY, 0G7E, 07A6; integral proper-base-change proof (1), (3),
steps 2 and 3 of the tensor-pull normalization argument.
(auxiliary; not a blueprint node).

Proof. Write P as the homotopy quotient of a cochain complex. Naturality of
`tX.derived` moves the exact pullback counit past the X tensor presentation.
Apply `TensorNormalized` on X, then the single-tensor comparison and symmetry,
to replace this composite by the restricted scalar computation counit and
ordinary balanced presentation. The exact restriction/pullback comparison
commutes with the exact computation counits. Apply `PullNormalized` to replace
`lam.hom`, followed by the X scalar counit, by the Y scalar counit followed by
the homotopy image of the ordinary balanced pullback comparison. The definition
of `scalarTensorRegularPullIso` makes the coefficient map exactly restriction
of the ordinary pullback unit. Apply `residueOrdinaryTensorPull_homotopy`, whose
signature allows arbitrary condensed coefficient maps. It identifies the
remaining balanced maps with ordinary pullback of the Y tensor presentation
followed by the ordinary tensorator. Identify the transported tensorator with
the native composite pullback tensorator by precomposing with the defining
balanced tensor coprojections: both maps pull back the two tensor factors,
and these coprojections are epimorphisms. Functoriality of Qh and naturality of the
exact pullback counit now give `scalarTensorPullModelMap`. This computation
uses no K-flatness: no tensor localization map is cancelled. -/
theorem scalar_pull_route_model (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (tX : TensorNormalization a X)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (hX : TensorNormalized a X tX) (hlam : PullNormalized a f lam)
    (P : HomotopyCategory (Modules Λ Y) (.up ℤ)) :
    (scalarTensorRestrictPullIso a f).hom.app ((D a Y).obj (DerivedCategory.Qh.obj P)) ≫
        (V a X).map (lam.hom.app (DerivedCategory.Qh.obj P)) ≫
        tX.derived.hom.app ((L Λ f).obj (DerivedCategory.Qh.obj P)) ≫
        scalarTensorPullModelTarget a f P = scalarTensorPullModelMap a f P := by
  unfold scalarTensorPullModelMap Functor.tensorModelMapWith
  dsimp only [id]
  exact scalar_route_pasting (L Λ f) DerivedCategory.Qh
    ((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh
    (pullCounit (Λ := Λ) f) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (scalar_pull_tensor_counit a f tX hX P)
    (IntegralResidueScalarCounitModel.tensorPresentation_app (coefficientMap a Y) P)
    (scalar_restriction_counit a f lam hlam P)
    (by simpa only [Category.assoc] using scalar_ordinary_tensor_pull_model a f P)

end AlgebraicGeometry.ProEtale.QuotientChange
