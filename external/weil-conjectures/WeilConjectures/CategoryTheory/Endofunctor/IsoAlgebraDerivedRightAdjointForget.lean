/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjoint

/-!
# The lifted right adjoint lies over the geometric one

In the setting of
`CategoryTheory.Endofunctor.IsoAlgebra.isLeftAdjoint_liftFullSubcategory_rightDerivedFunctor`,
let `R'` be a right adjoint of the restriction `RL : P_C ⥤ P_D` of the right derived functor of
`L : C ⥤ D`, and let `RW` be *any* right adjoint of the restriction of the right derived functor
of the lift `mapOfNatIso e : IsoAlgebra F ⥤ IsoAlgebra G`. Then the underlying object of `RW L'`
is `R'` of the underlying object of `L'`
(`CategoryTheory.Endofunctor.IsoAlgebra.nonempty_forget_obj_iso_of_adjunction`).

In the `ℓ`-adic formalism: the exceptional inverse image of Weil complexes, known only as an
abstract right adjoint, lies over the exceptional inverse image on the geometric fibres.

The object `H` with the universal arrow `d : RW H ⟶ L'` constructed in
`CategoryTheory.Endofunctor.IsoAlgebra.exists_bijective_rightDerivedFunctor_map_comp_free` and
`CategoryTheory.Endofunctor.IsoAlgebra.bijective_rightDerivedFunctor_map_comp` has underlying
object `R' (U L')`; by uniqueness of universal arrows, `H ≅ RW L'`.
-/

@[expose] public section

universe v v'

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type*} [Category.{v} C] [Abelian C]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {D : Type*} [Category.{v'} D] [Abelian D]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C]

/-- An object `H` of a full subcategory with a morphism `d : T H ⟶ Y` such that `u ↦ T u ≫ d`
is bijective on morphisms out of every object is isomorphic to `R Y`, for any right adjoint `R`
of `T`. -/
lemma nonempty_iso_obj_of_bijective {A B : Type*} [Category* A] [Category* B] {T : A ⥤ B}
    {R : B ⥤ A} (adj : T ⊣ R) {H : A} {Y : B} (d : T.obj H ⟶ Y)
    (hd : ∀ M, Function.Bijective (fun u : M ⟶ H ↦ T.map u ≫ d)) :
    Nonempty (H ≅ R.obj Y) := by
  let φ : ∀ M : A, (M ⟶ H) ≃ (M ⟶ R.obj Y) := fun M ↦
    (Equiv.ofBijective _ (hd M)).trans (adj.homEquiv M Y)
  have hφ : ∀ {M M' : A} (f : M' ⟶ M) (u : M ⟶ H), φ M' (f ≫ u) = f ≫ φ M u := by
    intro M M' f u
    simp only [φ, Equiv.trans_apply, Equiv.ofBijective_apply, Functor.map_comp, Category.assoc]
    exact adj.homEquiv_naturality_left _ _
  exact ⟨Yoneda.fullyFaithful.preimageIso (NatIso.ofComponents
    (fun M ↦ (φ M.unop).toIso) (fun {M M'} f ↦ by ext u; exact hφ f.unop u))⟩

/-- **The lifted right adjoint lies over the geometric one.** In the setting of
`CategoryTheory.Endofunctor.IsoAlgebra.isLeftAdjoint_liftFullSubcategory_rightDerivedFunctor`,
let `R'` be a right adjoint of the restriction `RL : P_C ⥤ P_D` and `RW` a right adjoint of the
restriction `R(mapOfNatIso e) : P_C^W ⥤ P_D^W`. Then for every `L'` in `P_D^W`, the underlying
object of `RW L'` is `R'` of the underlying object of `L'`. -/
theorem nonempty_forget_obj_iso_of_adjunction
    [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
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
    Nonempty ((forget F).mapDerivedCategory.obj (RW.obj L').obj ≅
      (R'.obj ⟨(forget G).mapDerivedCategory.obj L'.obj, (hPDW _).1 L'.property⟩).obj) := by
  obtain ⟨H, hH, ⟨eH⟩, d, hd⟩ := exists_bijective_rightDerivedFunctor_map_comp_free e PC PD hPC
    hR adj hPC_F hPD_G hcoprod L'.obj ((hPDW _).1 L'.property)
  let T := PCW.liftFullSubcategory PDW (mapOfNatIso e).rightDerivedFunctor hRW
  have hb (M : PCW.FullSubcategory) : Function.Bijective
      (fun u : M ⟶ ⟨H, (hPCW H).2 hH⟩ ↦ T.map u ≫ ObjectProperty.homMk d) := by
    have h := bijective_rightDerivedFunctor_map_comp e PC hPC_shift d hd M.obj
      ((hPCW _).1 M.property)
    refine ⟨fun u u' huu ↦ ObjectProperty.hom_ext _ (h.1 (congrArg InducedCategory.Hom.hom huu)),
      fun y ↦ ?_⟩
    obtain ⟨u, hu⟩ := h.2 y.hom
    exact ⟨ObjectProperty.homMk u, ObjectProperty.hom_ext _ hu⟩
  obtain ⟨i⟩ := nonempty_iso_obj_of_bijective adjW (H := ⟨H, (hPCW H).2 hH⟩) (Y := L')
    (ObjectProperty.homMk d) hb
  exact ⟨((forget F).mapDerivedCategory.mapIso ((ObjectProperty.ι _).mapIso i)).symm ≪≫ eH⟩

end CategoryTheory.Endofunctor.IsoAlgebra
