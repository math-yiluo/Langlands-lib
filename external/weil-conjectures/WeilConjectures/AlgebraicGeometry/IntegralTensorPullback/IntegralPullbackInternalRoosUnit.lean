/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralTensorPullbackData

import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.WeilObject.Sheaf.StalkUnit

set_option linter.privateModule false

/-! # Ordinary pullback and the actual completion augmentation

## References

* Stacks 099M
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  Mod.extendScalarsIsoComapInv
private def tensorSquareIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {N : C} {N' : D} (e : F.obj N ≅ N') :
    tensorRight N ⋙ F ≅ F ⋙ tensorRight N' :=
  (Functor.Monoidal.commTensorRight F N).symm ≪≫
    Functor.isoWhiskerLeft F ((tensoringRight D).mapIso e)

private def roosIso
    {C : Type*} [Category C] [Abelian C] {V V' : CochainComplex C ℤ}
    (t : V ⟶ V) (t' : V' ⟶ V') (a : V ≅ V') (ht : a.hom ≫ t' = t ≫ a.hom) :
    CochainComplex.mappingCocone t ≅ AdicCompletion.genericRoos V' t' :=
  AdicCompletion.genericCoconeIso V t ≪≫
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ biprod.mapIso
        ((HomologicalComplex.eval _ _ i).mapIso a)
        ((HomologicalComplex.eval _ _ (i - 1)).mapIso a)) (by
      intro i j hij
      obtain rfl : i + 1 = j := hij
      change biprod.map (a.hom.f i) (a.hom.f (i - 1)) ≫
          (AdicCompletion.genericRoos V' t').d i (i + 1) =
        (AdicCompletion.genericRoos V t).d i (i + 1) ≫
          biprod.map (a.hom.f (i + 1)) (a.hom.f (i + 1 - 1))
      simpa only [AdicCompletion.genericRoos, CochainComplex.of_d] using
        AdicCompletion.genericRoosMap_comm t t' a.hom ht i)

private abbrev pointUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :=
  @MonoidalCategoryStruct.tensorUnit
    (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) _
    MonoidalCategory.toMonoidalCategoryStruct

private def pointRegularIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :=
  (Functor.Monoidal.εIso (CondensedRing.upperStarFromPointMod Λ X)).symm

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private abbrev pull {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  CondensedRing.upperStar (DerivedNakayama.integerRing l E) g

private def pointComp {X Y : Scheme.{u}} (g : X ⟶ Y) :
    DerivedNakayama.pullback l E Y ⋙ pull l E g ≅ DerivedNakayama.pullback l E X :=
  CondensedRing.upperStarFromPointModComp (DerivedNakayama.integerRing l E) g

private def levelFunctorIso {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    tensorRight (AdicCompletion.finiteModule l E Y n) ⋙ pull l E g ≅
      pull l E g ⋙ tensorRight (AdicCompletion.finiteModule l E X n) :=
  tensorSquareIso (pull l E g)
    ((pointComp l E g).app (DerivedNakayama.quotientModule l E (n + 1)))

private def levelIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) (n : ℕ) :
    (pulledTower l E g P).obj (op n) ≅
      (AdicCompletion.level l E X n).obj
        (((pull l E g).mapHomologicalComplex (.up ℤ)).obj P) :=
  (Functor.mapHomologicalComplexCompIso (levelFunctorIso l E g n) (.up ℤ)).app P

end AlgebraicGeometry.ProEtale.IntegralTensorPullback
