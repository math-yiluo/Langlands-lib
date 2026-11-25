/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointForget

/-!
# The Weil structure of a right adjoint of Weil complexes is the exceptional datum

In the setting of `CategoryTheory.Endofunctor.IsoAlgebra.nonempty_forget_obj_iso_of_adjunction`,
let `R'` be a right adjoint of the restriction `RL : P_C ⥤ P_D` of the right derived functor of
`L`, and `RW` any right adjoint of the restriction `R(mapOfNatIso e) : P_C^W ⥤ P_D^W` of the
right derived functor of the lifted functor (for instance the exceptional inverse image `Rf^!`
of Weil complexes, an arbitrary right adjoint of `Rf₀!`). For an object `L'` of `P_D^W` with
underlying object `Y`, this file identifies the underlying object of `RW L'` with `R' Y`
*together with its Weil structure*:

- the identification `θ : U (RW L') ≅ R' Y` carries the underlying morphism of the counit
  `RW ⋙ R(mapOfNatIso e) ⟶ 𝟭` to the counit of `RL ⊣ R'`
  (`CategoryTheory.Endofunctor.IsoAlgebra.exists_forget_obj_iso_counit_comm`);
- a Weil datum `v : F (R' Y) ⟶ R' Y` for which the counit `RL (R' Y) ⟶ Y` is equivariant is
  unique (`CategoryTheory.Endofunctor.IsoAlgebra.eq_of_comm_counit`), hence the derived
  structure isomorphism of `RW L'` corresponds under `θ` to the *exceptional datum*, the unique
  such `v` (which `CategoryTheory.Endofunctor.IsoAlgebra.exists_iso_counit_isWeilEquivariant`
  provides as the mate of `e`).

This is the formal content of "the Frobenius structure of the Weil `Rf^!` is the exceptional
datum of the Frobenius square" (blueprint `proposition-purity-trace-commute-frobenius`): the
orientation of a smooth morphism is Frobenius equivariant as soon as it carries this
counit-characterized datum to the Tate datum.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v v'

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- An object `H` with a morphism `d : T H ⟶ Y` such that `u ↦ T u ≫ d` is bijective on
morphisms out of every object is isomorphic to `R Y`, for any right adjoint `R` of `T`, by an
isomorphism compatible with `d` and the counit. -/
lemma exists_iso_obj_counit_comp_eq_of_bijective {A B : Type*} [Category* A] [Category* B]
    {T : A ⥤ B} {R : B ⥤ A} (adj : T ⊣ R) {H : A} {Y : B} (d : T.obj H ⟶ Y)
    (hd : ∀ M, Function.Bijective (fun u : M ⟶ H ↦ T.map u ≫ d)) :
    ∃ i : H ≅ R.obj Y, T.map i.hom ≫ adj.counit.app Y = d := by
  obtain ⟨j, hj₀⟩ := (hd (R.obj Y)).2 (adj.counit.app Y)
  have hj : T.map j ≫ d = adj.counit.app Y := hj₀
  have hi : T.map (adj.homEquiv H Y d) ≫ adj.counit.app Y = d :=
    (adj.homEquiv H Y).symm_apply_apply d
  refine ⟨⟨adj.homEquiv H Y d, j, ?_, ?_⟩, hi⟩
  · apply (hd H).1
    simp only [Functor.map_comp, Category.assoc, hj, hi, CategoryTheory.Functor.map_id,
      Category.id_comp]
  · apply (adj.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      hi, hj, CategoryTheory.Functor.map_id, Category.id_comp]

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
/-- **Uniqueness of the exceptional datum**: two Weil data on `R' Y` for which the counit
`RL (R' Y) ⟶ Y` is equivariant (for the same datum on `Y`) are equal. -/
lemma eq_of_comm_counit (PC : ObjectProperty (DerivedCategory C))
    (PD : ObjectProperty (DerivedCategory D))
    (hR : ∀ K, PC K → PD (L.rightDerivedFunctor.obj K))
    {R' : PD.FullSubcategory ⥤ PC.FullSubcategory}
    (adj : PC.liftFullSubcategory PD L.rightDerivedFunctor hR ⊣ R')
    (hPC_F : ∀ K, PC (F.mapDerivedCategory.obj K) ↔ PC K)
    (Y : PD.FullSubcategory) {v v' : F.mapDerivedCategory.obj (R'.obj Y).obj ⟶ (R'.obj Y).obj}
    (h : (derivedCommIso e).hom.app (R'.obj Y).obj ≫ L.rightDerivedFunctor.map v ≫
        (adj.counit.app Y).hom =
      (derivedCommIso e).hom.app (R'.obj Y).obj ≫ L.rightDerivedFunctor.map v' ≫
        (adj.counit.app Y).hom) : v = v' :=
  (bijective_map_comp_counit_app_hom PC PD L.rightDerivedFunctor hR adj Y _
    ((hPC_F _).2 (R'.obj Y).property)).1 ((cancel_epi _).1 h)

/-- **The lifted counit on free algebras, with its Weil data.** The statement of
`CategoryTheory.Endofunctor.IsoAlgebra.exists_bijective_rightDerivedFunctor_map_comp_free`,
recording moreover the Weil datum `v` on `R' Y` for which the counit is equivariant, that the
derived structure isomorphism of `H` corresponds to `v` under `H ≅ R' Y`, and that `d` lifts the
counit. -/
theorem exists_bijective_rightDerivedFunctor_map_comp_free_weilDatum
    (PC : ObjectProperty (DerivedCategory C))
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
      (eH : (forget F).mapDerivedCategory.obj H ≅ (R'.obj ⟨_, hL'⟩).obj)
      (v : F.mapDerivedCategory.obj (R'.obj ⟨_, hL'⟩).obj ≅ (R'.obj ⟨_, hL'⟩).obj)
      (d : (mapOfNatIso e).rightDerivedFunctor.obj H ⟶ L'),
      ((derivedCommIso e).hom.app (R'.obj ⟨_, hL'⟩).obj ≫ L.rightDerivedFunctor.map v.hom ≫
          (adj.counit.app ⟨_, hL'⟩).hom =
        G.mapDerivedCategory.map (adj.counit.app ⟨_, hL'⟩).hom ≫
          (derivedStrIso G).hom.app L') ∧
      ((derivedStrIso F).hom.app H ≫ eH.hom = F.mapDerivedCategory.map eH.hom ≫ v.hom) ∧
      ((forget G).mapDerivedCategory.map d = (derivedForgetCommIso e).hom.app H ≫
        L.rightDerivedFunctor.map eH.hom ≫ (adj.counit.app ⟨_, hL'⟩).hom) ∧
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
  refine ⟨H, hH, eH, v, d, hv, hσ', hd, fun X hX ↦ ?_⟩
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

/-- **The Weil structure of a right adjoint of Weil complexes is the exceptional datum.** In the
setting of `nonempty_forget_obj_iso_of_adjunction`, for `L'` in `P_D^W` with underlying object
`Y`, there is an identification `θ : U (RW L') ≅ R' Y` of the underlying object of `RW L'` with
`R' Y` which carries the (underlying) counit of `RW` to the counit of `R'`, and the derived
structure isomorphism of `RW L'` to every Weil datum on `R' Y` for which the counit is
equivariant. -/
theorem exists_forget_obj_iso_counit_comm
    (PC : ObjectProperty (DerivedCategory C)) (PD : ObjectProperty (DerivedCategory D))
    [PC.IsClosedUnderIsomorphisms] [PD.IsClosedUnderIsomorphisms]
    (hPC : ∀ K, PC K → DerivedCategory.TStructure.t.bounded K)
    (hPC_shift : ∀ (K : DerivedCategory C) (n : ℤ), PC K → PC (K⟦n⟧))
    (hPC_F : ∀ K, PC (F.mapDerivedCategory.obj K) ↔ PC K)
    (hPD_G : ∀ K, PD K → PD (G.mapDerivedCategory.obj K))
    (hR : ∀ K, PC K → PD (L.rightDerivedFunctor.obj K))
    {R' : PD.FullSubcategory ⥤ PC.FullSubcategory}
    (adj : PC.liftFullSubcategory PD L.rightDerivedFunctor hR ⊣ R')
    (hcoprod : ∀ (X : ℤ → DerivedCategory C) (a : ℤ), (∀ n, (X n).IsGE a) →
      PreservesColimit (Discrete.functor X) L.rightDerivedFunctor)
    (PCW : ObjectProperty (DerivedCategory (IsoAlgebra F)))
    (PDW : ObjectProperty (DerivedCategory (IsoAlgebra G)))
    (hPCW : ∀ M, PCW M ↔ PC ((forget F).mapDerivedCategory.obj M))
    (hPDW : ∀ M, PDW M ↔ PD ((forget G).mapDerivedCategory.obj M))
    (hRW : ∀ M, PCW M → PDW ((mapOfNatIso e).rightDerivedFunctor.obj M))
    {RW : PDW.FullSubcategory ⥤ PCW.FullSubcategory}
    (adjW : PCW.liftFullSubcategory PDW (mapOfNatIso e).rightDerivedFunctor hRW ⊣ RW)
    (L' : PDW.FullSubcategory) :
    ∃ θ : (forget F).mapDerivedCategory.obj (RW.obj L').obj ≅
        (R'.obj ⟨(forget G).mapDerivedCategory.obj L'.obj, (hPDW _).1 L'.property⟩).obj,
      ((derivedForgetCommIso e).hom.app (RW.obj L').obj ≫ L.rightDerivedFunctor.map θ.hom ≫
          (adj.counit.app ⟨_, (hPDW _).1 L'.property⟩).hom =
        (forget G).mapDerivedCategory.map (adjW.counit.app L').hom) ∧
      ∀ v : F.mapDerivedCategory.obj
          (R'.obj ⟨(forget G).mapDerivedCategory.obj L'.obj, (hPDW _).1 L'.property⟩).obj ⟶
          (R'.obj ⟨(forget G).mapDerivedCategory.obj L'.obj, (hPDW _).1 L'.property⟩).obj,
        (derivedCommIso e).hom.app _ ≫ L.rightDerivedFunctor.map v ≫
            (adj.counit.app ⟨_, (hPDW _).1 L'.property⟩).hom =
          G.mapDerivedCategory.map (adj.counit.app ⟨_, (hPDW _).1 L'.property⟩).hom ≫
            (derivedStrIso G).hom.app L'.obj →
        F.mapDerivedCategory.map θ.hom ≫ v = (derivedStrIso F).hom.app (RW.obj L').obj ≫ θ.hom := by
  obtain ⟨H, hH, eH, v₀, d, hv₀, hσ, hd, hbij⟩ :=
    exists_bijective_rightDerivedFunctor_map_comp_free_weilDatum e PC PD hPC hR adj hPC_F hPD_G
      hcoprod L'.obj ((hPDW _).1 L'.property)
  let Y : PD.FullSubcategory := ⟨_, (hPDW _).1 L'.property⟩
  let RL := L.rightDerivedFunctor
  let RLW := (mapOfNatIso e).rightDerivedFunctor
  let T := PCW.liftFullSubcategory PDW RLW hRW
  let Hw : PCW.FullSubcategory := ⟨H, (hPCW H).2 hH⟩
  let dW : T.obj Hw ⟶ L' := ObjectProperty.homMk d
  have hb (M : PCW.FullSubcategory) : Function.Bijective
      (fun u : M ⟶ Hw ↦ T.map u ≫ dW) := by
    have h := bijective_rightDerivedFunctor_map_comp e PC hPC_shift d hbij M.obj
      ((hPCW _).1 M.property)
    refine ⟨fun u u' huu ↦ ObjectProperty.hom_ext _ (h.1 (congrArg InducedCategory.Hom.hom huu)),
      fun y ↦ ?_⟩
    obtain ⟨u, hu⟩ := h.2 y.hom
    exact ⟨ObjectProperty.homMk u, ObjectProperty.hom_ext _ hu⟩
  obtain ⟨i, hi⟩ := exists_iso_obj_counit_comp_eq_of_bijective adjW dW hb
  -- the underlying morphisms of `i` and of the counit
  have hi' : RLW.map i.hom.hom ≫ (adjW.counit.app L').hom = d :=
    congrArg InducedCategory.Hom.hom hi
  let θ : (forget F).mapDerivedCategory.obj (RW.obj L').obj ≅ (R'.obj Y).obj :=
    ((forget F).mapDerivedCategory.mapIso ((ObjectProperty.ι _).mapIso i)).symm ≪≫ eH
  have hθ : θ.hom = (forget F).mapDerivedCategory.map i.inv.hom ≫ eH.hom := rfl
  -- counit compatibility
  have hcounit : (derivedForgetCommIso e).hom.app (RW.obj L').obj ≫ RL.map θ.hom ≫
      (adj.counit.app Y).hom = (forget G).mapDerivedCategory.map (adjW.counit.app L').hom := by
    have hn := (derivedForgetCommIso e).hom.naturality i.inv.hom
    dsimp at hn
    rw [hθ, Functor.map_comp, Category.assoc, ← reassoc_of% hn, ← hd, ← Functor.map_comp, ← hi',
      ← Category.assoc, ← Functor.map_comp]
    change (forget G).mapDerivedCategory.map (RLW.map (i.inv ≫ i.hom).hom ≫ _) = _
    rw [Iso.inv_hom_id]
    change (forget G).mapDerivedCategory.map (RLW.map (𝟙 _) ≫ _) = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  refine ⟨θ, hcounit, fun v hv ↦ ?_⟩
  -- the transported structure of `RW L'` is counit-equivariant, hence equals `v`
  have hε : (adj.counit.app Y).hom =
      RL.map θ.inv ≫ (derivedForgetCommIso e).inv.app (RW.obj L').obj ≫
      (forget G).mapDerivedCategory.map (adjW.counit.app L').hom := by
    rw [← hcounit, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hnat : G.mapDerivedCategory.map
      ((forget G).mapDerivedCategory.map (adjW.counit.app L').hom) ≫
      (derivedStrIso G).hom.app L'.obj =
      (derivedStrIso G).hom.app (RLW.obj (RW.obj L').obj) ≫
        (forget G).mapDerivedCategory.map (adjW.counit.app L').hom :=
    (derivedStrIso G).hom.naturality (adjW.counit.app L').hom
  have hstr := derivedStrIso_hom_app_comp_derivedForgetCommIso e (RW.obj L').obj
  have hcomm : G.mapDerivedCategory.map (RL.map θ.inv) ≫
      (derivedCommIso e).hom.app ((forget F).mapDerivedCategory.obj (RW.obj L').obj) =
      (derivedCommIso e).hom.app (R'.obj Y).obj ≫ RL.map (F.mapDerivedCategory.map θ.inv) :=
    (derivedCommIso e).hom.naturality θ.inv
  have hstr' : (derivedCommIso e).hom.app ((forget F).mapDerivedCategory.obj (RW.obj L').obj) ≫
      RL.map ((derivedStrIso F).hom.app (RW.obj L').obj) =
      G.mapDerivedCategory.map ((derivedForgetCommIso e).inv.app (RW.obj L').obj) ≫
        (derivedStrIso G).hom.app (RLW.obj (RW.obj L').obj) ≫
        (derivedForgetCommIso e).hom.app (RW.obj L').obj := by
    rw [hstr, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have key : (derivedCommIso e).hom.app (R'.obj Y).obj ≫
      RL.map (F.mapDerivedCategory.map θ.inv ≫ (derivedStrIso F).hom.app (RW.obj L').obj ≫ θ.hom) ≫
        (adj.counit.app Y).hom =
      G.mapDerivedCategory.map (adj.counit.app Y).hom ≫ (derivedStrIso G).hom.app L'.obj := by
    rw [hε]
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% hcomm, reassoc_of% hstr', hnat, Iso.hom_inv_id_map_assoc,
      Iso.hom_inv_id_app_assoc]
  have := eq_of_comm_counit e PC PD hR adj hPC_F Y (key.trans hv.symm)
  rw [← this, Iso.hom_inv_id_map_assoc]

end CategoryTheory.Endofunctor.IsoAlgebra
