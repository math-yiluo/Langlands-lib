/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointFree
public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedActionRealization
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The counit of the lifted right adjoint on free algebras

In the setting of `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjoint`,
let `RL : P_C ⥤ P_D` (the restriction of the right derived functor of `L`) have a right adjoint
`R'`. For an object `L'` of the derived category of algebras of `G` whose underlying object `Y`
lies in `P_D`, the object `R' Y` carries a Weil structure
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_iso_counit_isWeilEquivariant`), is realized by an
object `H` of the derived category of algebras of `F`, and the counit lifts to a morphism
`d : RW H ⟶ L'`. For every `X ∈ P_C`, the map `u ↦ RW u ≫ d` on morphisms out of the free
algebra `I X` is bijective
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_bijective_rightDerivedFunctor_map_comp_free`).
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

omit [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)] in
/-- The right adjoint `R'` of the restriction `P_C ⥤ P_D` of `RL` carries Weil structures: for
an isomorphism `ψ : G Y ≅ Y`, there is an isomorphism `v : F (R' Y) ≅ R' Y` for which the counit
`RL (R' Y) ⟶ Y` is equivariant, the Weil structure on `RL (R' Y)` being transported along
`RL ⋙ G ≅ F ⋙ RL`:
```
G (RL (R' Y)) ≅ RL (F (R' Y)) --RL v--> RL (R' Y)
       |                                       |
  G (counit)                                 counit
       v                                       v
     G Y -----------------ψ-----------------> Y
```
-/
theorem exists_iso_counit_isWeilEquivariant (PC : ObjectProperty (DerivedCategory C))
    (PD : ObjectProperty (DerivedCategory D)) [PC.IsClosedUnderIsomorphisms]
    (hR : ∀ K, PC K → PD (L.rightDerivedFunctor.obj K))
    {R' : PD.FullSubcategory ⥤ PC.FullSubcategory}
    (adj : PC.liftFullSubcategory PD L.rightDerivedFunctor hR ⊣ R')
    (hPC_F : ∀ K, PC (F.mapDerivedCategory.obj K) ↔ PC K)
    (hPD_G : ∀ K, PD K → PD (G.mapDerivedCategory.obj K))
    (Y : PD.FullSubcategory) (ψ : G.mapDerivedCategory.obj Y.obj ≅ Y.obj) :
    ∃ v : F.mapDerivedCategory.obj (R'.obj Y).obj ≅ (R'.obj Y).obj,
      (derivedCommIso e).hom.app (R'.obj Y).obj ≫ L.rightDerivedFunctor.map v.hom ≫
          (adj.counit.app Y).hom =
        G.mapDerivedCategory.map (adj.counit.app Y).hom ≫ ψ.hom := by
  let α := PC.liftFullSubcategory PC F.mapDerivedCategory fun K hK ↦ (hPC_F K).2 hK
  let β := PD.liftFullSubcategory PD G.mapDerivedCategory hPD_G
  have : α.EssSurj := ⟨fun K ↦ by
    have hK : PC (F.mapDerivedCategory.objPreimage K.obj) :=
      (hPC_F _).1 (PC.prop_of_iso (F.mapDerivedCategory.objObjPreimageIso K.obj).symm K.property)
    exact ⟨⟨_, hK⟩, ⟨ObjectProperty.isoMk _ (F.mapDerivedCategory.objObjPreimageIso K.obj)⟩⟩⟩
  have : α.IsEquivalence := {}
  let eres : PC.liftFullSubcategory PD L.rightDerivedFunctor hR ⋙ β ≅
      α ⋙ PC.liftFullSubcategory PD L.rightDerivedFunctor hR :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ ((derivedCommIso e).app K.obj))
      fun f ↦ ObjectProperty.hom_ext _ ((derivedCommIso e).hom.naturality f.hom)
  let ψ' : β.obj Y ⟶ Y := ObjectProperty.homMk ψ.hom
  have : IsIso ψ' := (PD.isoMk (X := β.obj Y) (Y := Y) ψ).isIso_hom
  have : IsIso ((Adjunction.rightAdjointExchange adj adj eres).app Y) :=
    Adjunction.isIso_rightAdjointExchange_app adj eres Y
  have : IsIso (Adjunction.rightWeilDatum adj eres ψ') := by
    rw [Adjunction.rightWeilDatum]
    infer_instance
  refine ⟨PC.ι.mapIso (asIso (Adjunction.rightWeilDatum adj eres ψ')), ?_⟩
  have h := Adjunction.isWeilEquivariant_counit adj eres ψ'
  rw [IsWeilEquivariant, Adjunction.leftWeilDatum] at h
  have h' := congrArg InducedCategory.Hom.hom h
  simp only [ObjectProperty.FullSubcategory.comp_hom] at h'
  rw [Category.assoc] at h'
  exact h'.symm

omit [Abelian C] [IsGrothendieckAbelian.{v} C] [F.Additive] [F.IsEquivalence] [Abelian D]
  [IsGrothendieckAbelian.{v'} D] [G.Additive] [G.IsEquivalence] [L.Additive]
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C] in
/-- For an adjunction between full subcategories whose left adjoint is induced by a functor `T`,
the adjunction bijection on underlying morphisms: `v ↦ T v ≫ ε` is bijective. -/
lemma bijective_map_comp_counit_app_hom {A B : Type*} [Category* A] [Category* B]
    (PA : ObjectProperty A) (PB : ObjectProperty B) (T : A ⥤ B) (h : ∀ X, PA X → PB (T.obj X))
    {R' : PB.FullSubcategory ⥤ PA.FullSubcategory} (adj : PA.liftFullSubcategory PB T h ⊣ R')
    (Y : PB.FullSubcategory) (X : A) (hX : PA X) :
    Function.Bijective (fun v : X ⟶ (R'.obj Y).obj ↦ T.map v ≫ (adj.counit.app Y).hom) := by
  have hc (g : (⟨X, hX⟩ : PA.FullSubcategory) ⟶ R'.obj Y) :
      ((adj.homEquiv _ _).symm g).hom = T.map g.hom ≫ (adj.counit.app Y).hom := by
    rw [Adjunction.homEquiv_counit]
    rfl
  constructor
  · intro v v' hv
    have := (adj.homEquiv _ _).symm.injective (ObjectProperty.hom_ext _
      (((hc (PA.homMk v)).trans hv).trans (hc (PA.homMk v')).symm))
    exact congrArg InducedCategory.Hom.hom this
  · intro y
    refine ⟨(adj.homEquiv ⟨X, hX⟩ Y (PB.homMk y)).hom, ?_⟩
    have := congrArg InducedCategory.Hom.hom ((adj.homEquiv ⟨X, hX⟩ Y).symm_apply_apply
      (PB.homMk y))
    rw [hc] at this
    exact this


/-- **The lifted counit on free algebras.** For an object `L'` of the derived category of
algebras of `G` whose underlying object lies in `P_D`, there are an object `H` of the derived
category of algebras of `F` whose underlying object is isomorphic to `R' Y` (hence lies in `P_C`),
`Y` being the underlying object of `L'`, and a morphism
`d : RW H ⟶ L'` such that `u ↦ RW u ≫ d` is bijective on morphisms `I X ⟶ H` out of free
algebras on objects `X ∈ P_C`. Here `H` realizes `R' Y` with its Weil structure, and `d` lifts
the counit `RL (R' Y) ⟶ Y`. -/
theorem exists_bijective_rightDerivedFunctor_map_comp_free (PC : ObjectProperty (DerivedCategory C))
    (PD : ObjectProperty (DerivedCategory D)) [PC.IsClosedUnderIsomorphisms]
    (hPC : ∀ K, PC K → DerivedCategory.TStructure.t.bounded K)
    (hR : ∀ K, PC K → PD (L.rightDerivedFunctor.obj K))
    {R' : PD.FullSubcategory ⥤ PC.FullSubcategory}
    (adj : PC.liftFullSubcategory PD L.rightDerivedFunctor hR ⊣ R')
    (hPC_F : ∀ K, PC (F.mapDerivedCategory.obj K) ↔ PC K)
    (hPD_G : ∀ K, PD K → PD (G.mapDerivedCategory.obj K))
    (hcoprod : ∀ (X : ℤ → DerivedCategory C) (a : ℤ), (∀ n, (X n).IsGE a) →
      PreservesColimit (Discrete.functor X) L.rightDerivedFunctor)
    (L' : DerivedCategory (IsoAlgebra G)) (hL' : PD ((forget G).mapDerivedCategory.obj L')) :
    ∃ (H : DerivedCategory (IsoAlgebra F)) (_ : PC ((forget F).mapDerivedCategory.obj H))
      (_ : Nonempty ((forget F).mapDerivedCategory.obj H ≅ (R'.obj ⟨_, hL'⟩).obj))
      (d : (mapOfNatIso e).rightDerivedFunctor.obj H ⟶ L'),
      ∀ X, PC X → Function.Bijective
        (fun u : (Free.functor F).mapDerivedCategory.obj X ⟶ H ↦
          (mapOfNatIso e).rightDerivedFunctor.map u ≫ d) := by
  let RL := L.rightDerivedFunctor
  let Y : PD.FullSubcategory := ⟨_, hL'⟩
  let N := (R'.obj Y).obj
  have hN : PC N := (R'.obj Y).property
  let ε : RL.obj N ⟶ (forget G).mapDerivedCategory.obj L' := (adj.counit.app Y).hom
  obtain ⟨v, hv⟩ := exists_iso_counit_isWeilEquivariant e PC PD hR adj hPC_F hPD_G Y
    ((derivedStrIso G).app L')
  obtain ⟨H, eH, hσ, -, -⟩ := exists_cyclicDerivedActionRealization F N (hPC N hN) v
  have hσ' : (derivedStrIso F).hom.app H ≫ eH.hom = F.mapDerivedCategory.map eH.hom ≫ v.hom :=
    hσ
  have hH : PC ((forget F).mapDerivedCategory.obj H) := PC.prop_of_iso eH.symm hN
  let c := (derivedForgetCommIso e).hom.app H ≫ RL.map eH.hom ≫ ε
  have hc : (derivedStrIso G).hom.app ((mapOfNatIso e).rightDerivedFunctor.obj H) ≫ c =
      G.mapDerivedCategory.map c ≫ (derivedStrIso G).hom.app L' := by
    have hχ := (derivedCommIso e).hom.naturality eH.hom
    dsimp at hχ
    have hv' : (derivedCommIso e).hom.app N ≫ RL.map v.hom ≫ ε =
        G.mapDerivedCategory.map ε ≫ (derivedStrIso G).hom.app L' := hv
    simp only [c, Functor.map_comp, Category.assoc]
    rw [reassoc_of% (derivedStrIso_hom_app_comp_derivedForgetCommIso e H),
      ← Functor.map_comp_assoc, hσ', Functor.map_comp, Category.assoc, ← reassoc_of% hχ, hv']
  obtain ⟨d, hd⟩ := exists_forget_mapDerivedCategory_map_eq G c hc
  refine ⟨H, hH, ⟨eH⟩, d, fun X hX ↦ ?_⟩
  obtain ⟨a, ha⟩ := (hPC X hX).1
  have : X.IsGE a := ha
  have : IsIso (derivedFreeComparison e X) := isIso_derivedFreeComparison e hcoprod X a
  let adjF := freeWeilDerivedAdjunction F
  let adjG := freeWeilDerivedAdjunction G
  have key (u : (Free.functor F).mapDerivedCategory.obj X ⟶ H) :
      (mapOfNatIso e).rightDerivedFunctor.map u ≫ d = inv (derivedFreeComparison e X) ≫
        (adjG.homEquiv _ _).symm (RL.map (adjF.homEquiv _ _ u ≫ eH.hom) ≫ ε) := by
    rw [IsIso.eq_inv_comp]
    apply (adjG.homEquiv _ _).injective
    have hβ := (derivedForgetCommIso e).inv.naturality u
    dsimp at hβ
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp, hd,
      unit_app_comp_map_derivedFreeComparison_assoc, Adjunction.homEquiv_unit, ← reassoc_of% hβ]
    simp only [c, Iso.inv_hom_id_app_assoc, Functor.map_comp, Category.assoc]
    rfl
  have hfun : (fun u : (Free.functor F).mapDerivedCategory.obj X ⟶ H ↦
      (mapOfNatIso e).rightDerivedFunctor.map u ≫ d) =
      (fun y ↦ inv (derivedFreeComparison e X) ≫ y) ∘ (adjG.homEquiv _ _).symm ∘
        (fun w ↦ RL.map w ≫ ε) ∘ (fun w ↦ w ≫ eH.hom) ∘ (adjF.homEquiv _ _) :=
    funext key
  rw [hfun]
  refine Function.Bijective.comp ?_ ((Equiv.bijective _).comp
    ((bijective_map_comp_counit_app_hom PC PD RL hR adj Y X hX).comp
      (Function.Bijective.comp ?_ (Equiv.bijective _))))
  · exact ⟨fun y y' h ↦ (cancel_epi _).1 h, fun y ↦ ⟨derivedFreeComparison e X ≫ y, by simp⟩⟩
  · exact ⟨fun w w' h ↦ (cancel_mono eH.hom).1 h, fun y ↦ ⟨y ≫ eH.inv, by simp⟩⟩

end CategoryTheory.Endofunctor.IsoAlgebra
