/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointCoproduct
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# The right derived transport of algebras commutes with free algebras

Let `F`, `G` be exact autoequivalences of Grothendieck abelian categories `C`, `D` and let
`L : C ⥤ D` be additive with `e : L ⋙ G ≅ F ⋙ L`. Write `RW` for the total right derived
functor of `IsoAlgebra.mapOfNatIso e`, `RL` for that of `L`, `U` for the functors induced by the
forgetful functors and `I` for those induced by the free algebra functors.

- `CategoryTheory.Endofunctor.IsoAlgebra.derivedForgetCommIso`: `RW ⋙ U ≅ U ⋙ RL`;
- `CategoryTheory.Endofunctor.IsoAlgebra.derivedCommIso`: `RL ⋙ G ≅ F ⋙ RL`;
- `CategoryTheory.Endofunctor.IsoAlgebra.derivedStrIso_hom_app_comp_derivedForgetCommIso`: the
  first isomorphism is compatible with the derived structure isomorphisms via the second one;
- `CategoryTheory.Endofunctor.IsoAlgebra.isIso_derivedFreeComparison`: if `RL` preserves
  coproducts of uniformly bounded below families, then the canonical morphism
  `I (RL X) ⟶ RW (I X)` is an isomorphism for every bounded below `X`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v v'

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {D : Type*} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C]

/-- The isomorphism `RW ⋙ U ≅ U ⋙ RL`: right derivation commutes with forgetting the algebra
structures. -/
def derivedForgetCommIso :
    (mapOfNatIso e).rightDerivedFunctor ⋙ (forget G).mapDerivedCategory ≅
      (forget F).mapDerivedCategory ⋙ L.rightDerivedFunctor :=
  Functor.rightDerivedFunctorCommIso (mapOfNatIsoCompForgetIso e)

/-- The isomorphism `RL ⋙ G ≅ F ⋙ RL` induced by `e`. -/
def derivedCommIso :
    L.rightDerivedFunctor ⋙ G.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ L.rightDerivedFunctor :=
  Functor.rightDerivedFunctorCommIso e

/-- The isomorphism `RW ⋙ U ≅ U ⋙ RL` is compatible with the derived structure isomorphisms:
the derived structure isomorphism of `RW A` corresponds to `RL` of that of `A`, via
`RL ⋙ G ≅ F ⋙ RL`. -/
lemma derivedStrIso_hom_app_comp_derivedForgetCommIso (A : DerivedCategory (IsoAlgebra F)) :
    (derivedStrIso G).hom.app ((mapOfNatIso e).rightDerivedFunctor.obj A) ≫
        (derivedForgetCommIso e).hom.app A =
      G.mapDerivedCategory.map ((derivedForgetCommIso e).hom.app A) ≫
        (derivedCommIso e).hom.app ((forget F).mapDerivedCategory.obj A) ≫
        L.rightDerivedFunctor.map ((derivedStrIso F).hom.app A) := by
  have h := Functor.rightDerivedFunctorCommIso_hom_app_comp e (mapOfNatIsoCompForgetIso e)
    (mapOfNatIsoCompForgetIso e) (strNatIso F) (strNatIso G) (fun K ↦ by
      rw [← cancel_epi ((strNatIso G).hom.app ((mapOfNatIso e).obj K)), Iso.hom_inv_id_app_assoc,
        strNatIso_hom_app, mapOfNatIso_obj_str]
      simp [mapOfNatIsoCompForgetIso]) A
  simp only [derivedStrIso, derivedForgetCommIso, derivedCommIso]
  conv_lhs => rw [h]
  simp only [Iso.hom_inv_id_app_assoc]

/-- The compatibility `derivedStrIso_hom_app_comp_derivedForgetCommIso` in the form used to
transport the structure isomorphisms along the inverse of `RW ⋙ U ≅ U ⋙ RL`. -/
@[reassoc]
lemma map_derivedStrIso_hom_app_comp_derivedForgetCommIso_inv
    (A : DerivedCategory (IsoAlgebra F)) :
    L.rightDerivedFunctor.map ((derivedStrIso F).hom.app A) ≫
        (derivedForgetCommIso e).inv.app A =
      (derivedCommIso e).inv.app ((forget F).mapDerivedCategory.obj A) ≫
        G.mapDerivedCategory.map ((derivedForgetCommIso e).inv.app A) ≫
        (derivedStrIso G).hom.app ((mapOfNatIso e).rightDerivedFunctor.obj A) := by
  rw [← cancel_epi ((derivedCommIso e).hom.app _),
    ← cancel_epi (G.mapDerivedCategory.map ((derivedForgetCommIso e).hom.app A)),
    ← reassoc_of% (derivedStrIso_hom_app_comp_derivedForgetCommIso e A),
    Iso.hom_inv_id_app]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
  exact Category.comp_id _

/-- The canonical comparison `I (RL X) ⟶ RW (I X)` of free algebras: the morphism of free
algebras adjoint to `RL X ⟶ RL (U (I X)) ≅ U (RW (I X))`, induced by the unit of the free
adjunction. -/
def derivedFreeComparison (X : DerivedCategory C) :
    (Free.functor G).mapDerivedCategory.obj (L.rightDerivedFunctor.obj X) ⟶
      (mapOfNatIso e).rightDerivedFunctor.obj ((Free.functor F).mapDerivedCategory.obj X) :=
  ((freeWeilDerivedAdjunction G).homEquiv _ _).symm
    (L.rightDerivedFunctor.map ((freeWeilDerivedAdjunction F).unit.app X) ≫
      (derivedForgetCommIso e).inv.app ((Free.functor F).mapDerivedCategory.obj X))

@[reassoc]
lemma unit_app_comp_map_derivedFreeComparison (X : DerivedCategory C) :
    (freeWeilDerivedAdjunction G).unit.app (L.rightDerivedFunctor.obj X) ≫
        (forget G).mapDerivedCategory.map (derivedFreeComparison e X) =
      L.rightDerivedFunctor.map ((freeWeilDerivedAdjunction F).unit.app X) ≫
        (derivedForgetCommIso e).inv.app ((Free.functor F).mapDerivedCategory.obj X) := by
  exact ((freeWeilDerivedAdjunction G).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- **`RW` commutes with free algebras on bounded below objects.** If `RL` preserves coproducts
of uniformly bounded below families, then the comparison `I (RL X) ⟶ RW (I X)` is an
isomorphism for every bounded below object `X`:
```
I (RL X) --derivedFreeComparison--> RW (I X)
   |                                   |
   U                                   U
   v                                   v
 ∐ₙ Gⁿ (RL X) ≅ ∐ₙ RL (Fⁿ X) ----≅----> RL (∐ₙ Fⁿ X)
```
-/
theorem isIso_derivedFreeComparison
    (hcoprod : ∀ (X : ℤ → DerivedCategory C) (a : ℤ), (∀ n, (X n).IsGE a) →
      PreservesColimit (Discrete.functor X) L.rightDerivedFunctor)
    (X : DerivedCategory C) (a : ℤ) [X.IsGE a] : IsIso (derivedFreeComparison e X) := by
  have : (forget G).mapDerivedCategory.ReflectsIsomorphisms :=
    (freeWeil_derived_properties G).2.2.2.1
  suffices IsIso ((forget G).mapDerivedCategory.map (derivedFreeComparison e X)) from
    isIso_of_reflects_iso _ (forget G).mapDerivedCategory
  let RL := L.rightDerivedFunctor
  let Z := RL.obj X
  have : PreservesColimit
      (Discrete.functor fun n ↦ (Free.objFunctor F n).mapDerivedCategory.obj X) RL :=
    hcoprod _ a fun n ↦ Functor.isGE_mapDerivedCategory_obj _ X a
  have hd₀ := (isColimitMapCoconeCofanMkEquiv RL _ _)
    (isColimitOfPreserves RL (isColimitDerivedFreeCofan F X))
  let q (n : ℤ) := RL.map ((derivedFreeSummand F n).app X) ≫
    (derivedForgetCommIso e).inv.app ((Free.functor F).mapDerivedCategory.obj X)
  have hd : IsColimit (Cofan.mk _ q) :=
    isColimitCofanMkOfIso hd₀ (fun n ↦ Iso.refl _)
      ((derivedForgetCommIso e).app ((Free.functor F).mapDerivedCategory.obj X))
      (fun n ↦ by
        simp only [q, Category.assoc, Iso.app_hom, Iso.inv_hom_id_app, Iso.refl_hom,
          Category.id_comp]
        exact Category.comp_id _)
  obtain ⟨ζG, hζG⟩ := exists_iso_derivedFreeSummand_zero G Z
  obtain ⟨ζF, hζF⟩ := exists_iso_derivedFreeSummand_zero F X
  have ht (n : ℤ) := exists_iso_summand_comp_eq G.mapDerivedCategory
    (fun n ↦ (derivedFreeSummand G n).app Z) q
    ((derivedStrIso G).hom.app ((Free.functor G).mapDerivedCategory.obj Z))
    ((derivedStrIso G).hom.app
      ((mapOfNatIso e).rightDerivedFunctor.obj ((Free.functor F).mapDerivedCategory.obj X)))
    (fun n ↦ (derivedFreeSummandSuccIso G n).app Z)
    (fun n ↦ RL.mapIso ((derivedFreeSummandSuccIso F n).app X) ≪≫
      ((derivedCommIso e).app _).symm)
    (fun n ↦ derivedFreeSummand_succ G n Z)
    (fun n ↦ by
      simp only [q, derivedFreeSummand_succ F n X, Functor.map_comp, Category.assoc,
        Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv]
      rw [map_derivedStrIso_hom_app_comp_derivedForgetCommIso_inv]
      erw [(derivedCommIso e).inv.naturality_assoc]
      rfl)
    ((forget G).mapDerivedCategory.map (derivedFreeComparison e X))
    ((derivedStrIso G).hom.naturality (derivedFreeComparison e X))
    (ζG ≪≫ RL.mapIso ζF.symm)
    (by
      simp only [hζG, q, hζF, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
        ← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]
      exact congrArg (ζG.hom ≫ ·) (unit_app_comp_map_derivedFreeComparison e X))
    n
  choose t ht using ht
  exact isIso_of_cofan_inj_comp_eq (isColimitDerivedFreeCofan G Z) hd _ t ht

end CategoryTheory.Endofunctor.IsoAlgebra
