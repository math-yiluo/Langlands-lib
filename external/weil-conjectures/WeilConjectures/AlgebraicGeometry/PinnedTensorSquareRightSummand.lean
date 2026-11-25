/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.PinnedTensorSquareLeftSummand
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.AlgebraicGeometry.PinnedStalkTensor

/-! # Stalk compatibility of a specified tensor pullback chain map

Source: Stacks Project, perfect.tex, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-pinned-tensor-square-right-summand).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry

local instance pinnedTensorSquareRightSummandInstance1 (Y : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  pullbackDescentModuleTensor Y

local instance pinnedTensorSquareRightSummandInstance2 (Y : Scheme.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  modulePreadditive Y

attribute [local instance] pinnedTensorSquareLeftSummandInstance3
  pinnedTensorSquareLeftSummandInstance4

private theorem extendScalars_tensor_summand
    {A B : Type u} [CommRing A] [CommRing B] (b : A →+* B)
    (U V : CochainComplex (ModuleCat.{u} A) ℤ)
    {U' V' W T : CochainComplex (ModuleCat.{u} B) ℤ}
    (α : ((ModuleCat.extendScalars b).mapHomologicalComplex (.up ℤ)).obj U ⟶ U')
    (β : ((ModuleCat.extendScalars b).mapHomologicalComplex (.up ℤ)).obj V ⟶ V')
    (γ : V' ⟶ W) (θ : U' ⊗ W ⟶ T) (n p q : ℤ) (h : p + q = n) :
    let G := ModuleCat.extendScalars b
    let F := G.mapHomologicalComplex (.up ℤ)
    G.map (HomologicalComplex.ιMapBifunctor U V (curriedTensor _) (.up ℤ) p q n h) ≫
        (Functor.OplaxMonoidal.δ F U V ≫ (F.obj U ◁ (β ≫ γ)) ≫
          (α ⊗ₘ 𝟙 W) ≫ θ).f n =
      Functor.OplaxMonoidal.δ G (U.X p) (V.X q) ≫ (α.f p ⊗ₘ β.f q) ≫
        (𝟙 _ ⊗ₘ γ.f q) ≫
        HomologicalComplex.ιMapBifunctor U' W (curriedTensor _) (.up ℤ) p q n h ≫
        θ.f n := by
  dsimp only
  simp only [HomologicalComplex.comp_f, Functor.mapCochainComplex_δ,
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
    HomologicalComplex.mapBifunctorComparison_f]
  erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  erw [CochainComplex.ιTensorObj_whiskerLeft_f_assoc,
    HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f, HomologicalComplex.comp_f]
  simp only [HomologicalComplex.mapBifunctorComparisonApp,
    Functor.OplaxMonoidal.δNatTrans, curriedTensor, tensorHom_def, whiskerLeft_comp,
    Category.assoc, id_whiskerRight]
  rw [whisker_exchange_assoc, whisker_exchange_assoc]
  simp only [whiskerLeft_id, Category.id_comp]
  rfl

/-- Scalar-tensor route on one summand, in explicit stalk coordinates.

Proof: expand the complex tensorator as the total-complex oplax comparison and use
its summand equation, which is the module tensorator followed by the target injection.
The whiskerLeft summand equation moves t to its degree-q component. The bifunctor-map
summand equation moves the tensor of κ_P with the identity to its degree-p component.
Expand t, distribute whiskerLeft over composition, and apply whisker_exchange twice.
Identity whiskerings cancel. This gives the stated module tensorator, followed by
κ_P,p tensor κ_Q,q, identity tensor S(a)_q, the stalk-complex tensor injection, and the
inverse pinned target comparison. No hypothesis on χ is used. Empty and infinite
coproducts and zero modules require no special case: the equation is on one summand.
Source: Stacks Project, perfect.tex, Tag 0DJA(1), local tensor comparison calculation.
(blueprint: lem-pc-pinned-tensor-square-right-summand). -/
theorem pinned_tensor_square_right_summand
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) ℤ)
    (a : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q ⟶ N)
    (z : X') (n p q : ℤ) (h : p + q = n) :
    letI := SingleComplexBaseChange.leftAlgebra f g' z
    letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
    letI := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
    let R := SingleComplexBaseChange.R f g' z
    let A := SingleComplexBaseChange.A g' z
    let B := SingleComplexBaseChange.B f' z
    let C := SingleComplexBaseChange.C z
    let F := (ModuleCat.extendScalars.{u, u, u}
      ((algebraMap (TensorProduct R A B) C).comp
        (algebraMap A (TensorProduct R A B)))).mapHomologicalComplex (.up ℤ)
    let S := (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
      (.up ℤ)
    let U := SingleComplexBaseChange.stalkComplex g' z P
    let V := SingleComplexBaseChange.stalkComplex g' z Q
    let t := (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z Q).hom ≫ S.map a
    let H := (Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)
    let e' := Classical.choose (exists_pinned_stalk_tensor X' z)
    let ρ : F.obj U ⊗ S.obj N ≅ S.obj (pullbackTensorTotal X' (H.obj P) N) :=
      tensorIso (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z P)
        (Iso.refl (S.obj N)) ≪≫ (e' (H.obj P) N).symm
    let G := ModuleCat.extendScalars.{u, u, u}
      ((algebraMap (TensorProduct R A B) C).comp
        (algebraMap A (TensorProduct R A B)))
    let ι := G.map (HomologicalComplex.ιMapBifunctor U V
      (curriedTensor _) (.up ℤ) p q n h)
    ι ≫ ((Functor.Monoidal.μIso F U V).inv ≫ (F.obj U ◁ t) ≫ ρ.hom).f n =
      Functor.OplaxMonoidal.δ G (U.X p) (V.X q) ≫
      ((SingleComplexBaseChange.tensorStalkIso f f' g g' sq z P).hom.f p ⊗ₘ
        (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z Q).hom.f q) ≫
      (𝟙 _ ⊗ₘ (S.map a).f q) ≫
      HomologicalComplex.ιMapBifunctor (S.obj (H.obj P)) (S.obj N)
        (curriedTensor _) (.up ℤ) p q n h ≫ (e' (H.obj P) N).inv.f n  := by
  extract_lets R A B C F S U V t H e' ρ G ι
  exact extendScalars_tensor_summand _ U V
    (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z P).hom
    (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z Q).hom
    (S.map a) (e' (H.obj P) N).inv n p q h


end AlgebraicGeometry
