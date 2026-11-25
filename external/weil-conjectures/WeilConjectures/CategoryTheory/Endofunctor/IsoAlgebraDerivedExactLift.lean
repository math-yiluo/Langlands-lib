/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointLift
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentation
public import WeilConjectures.CategoryTheory.WeilEquivariance

/-!
# The derived transport of Weil structures along an exact functor

Let `L : C ⥤ D` be an exact functor with an exchange `e : L ⋙ G ≅ F ⋙ L` against endofunctors
`F`, `G`, and let `T = mapOfNatIso e : IsoAlgebra F ⥤ IsoAlgebra G` be the transport of
structures (for `L = φ̄^*` a pullback along a morphism of `k₀`-schemes, `T = φ^*` on Weil
sheaves). On derived categories, `D(T)` lies over `D(L)` through
`CategoryTheory.Endofunctor.IsoAlgebra.derivedExactForgetCommIso : D(T) ⋙ D(U_G) ≅ D(U_F) ⋙ D(L)`
and the derived exchange `CategoryTheory.Endofunctor.IsoAlgebra.derivedExactCommIso :
D(L) ⋙ D(G) ≅ D(F) ⋙ D(L)`: the derived structure isomorphism of `D(T) M` is the transport of
that of `M`
(`CategoryTheory.Endofunctor.IsoAlgebra.derivedStrIso_hom_app_comp_derivedExactForgetCommIso`).
This is the derived form of `mapOfNatIso_obj_str`, proved by the presentation calculus of
`CategoryTheory.Functor.DerivedRepresents`.
-/

@[expose] public noncomputable section

universe v v' w w'

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

open Functor.DerivedPresentation

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type*} [Category.{v} C] [Abelian C] {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {D : Type*} [Category.{v'} D] [Abelian D] {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (IsoAlgebra F)]
  [HasDerivedCategory.{w'} D] [HasDerivedCategory.{w'} (IsoAlgebra G)]

/-- The derived exchange `D(L) ⋙ D(G) ≅ D(F) ⋙ D(L)` induced by `e`. -/
def derivedExactCommIso :
    L.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ L.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso L G ≪≫ Functor.mapDerivedCategoryNatIso e) ≪≫
    (Functor.mapDerivedCategoryCompIso F L).symm

/-- The derived transport `D(T)` lies over `D(L)`: `D(T) ⋙ D(U_G) ≅ D(U_F) ⋙ D(L)`. -/
def derivedExactForgetCommIso :
    (mapOfNatIso e).mapDerivedCategory ⋙ (forget G).mapDerivedCategory ≅
      (forget F).mapDerivedCategory ⋙ L.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (mapOfNatIso e) (forget G) ≪≫
    Functor.mapDerivedCategoryNatIso (mapOfNatIsoCompForgetIso e)) ≪≫
    (Functor.mapDerivedCategoryCompIso (forget F) L).symm

/-- **The derived structure of a transported object is the transport of the structure**: for
`M` in `D(IsoAlgebra F)`, the derived structure isomorphism of `D(T) M` corresponds, through
`D(T) ⋙ D(U_G) ≅ D(U_F) ⋙ D(L)`, to the derived exchange followed by `D(L)` of the derived
structure isomorphism of `M`. -/
theorem derivedStrIso_hom_app_comp_derivedExactForgetCommIso
    (M : DerivedCategory (IsoAlgebra F)) :
    (derivedStrIso G).hom.app ((mapOfNatIso e).mapDerivedCategory.obj M) ≫
        (derivedExactForgetCommIso e).hom.app M =
      G.mapDerivedCategory.map ((derivedExactForgetCommIso e).hom.app M) ≫
        (derivedExactCommIso e).hom.app ((forget F).mapDerivedCategory.obj M) ≫
        L.mapDerivedCategory.map ((derivedStrIso F).hom.app M) := by
  have hσG : Functor.DerivedRepresents ((ofMap (forget G)).comp (ofMap G)) (ofMap (forget G))
      (derivedStrIso G).hom (strNatIso G).hom :=
    Functor.derivedRepresents_mapDerivedCategoryCompIso_symm_trans (strNatIso G)
  have hσF : Functor.DerivedRepresents ((ofMap (forget F)).comp (ofMap F)) (ofMap (forget F))
      (derivedStrIso F).hom (strNatIso F).hom :=
    Functor.derivedRepresents_mapDerivedCategoryCompIso_symm_trans (strNatIso F)
  have hκ : Functor.DerivedRepresents ((ofMap (mapOfNatIso e)).comp (ofMap (forget G)))
      ((ofMap (forget F)).comp (ofMap L)) (derivedExactForgetCommIso e).hom
      ((mapOfNatIsoCompForgetIso e).hom ≫ 𝟙 _) :=
    (Functor.derivedRepresents_mapDerivedCategoryCompIso_symm_trans
      (mapOfNatIsoCompForgetIso e)).comp
      (Functor.derivedRepresents_mapDerivedCategoryCompIso (forget F) L)
  have he : Functor.DerivedRepresents ((ofMap L).comp (ofMap G)) ((ofMap F).comp (ofMap L))
      (derivedExactCommIso e).hom (e.hom ≫ 𝟙 _) :=
    (Functor.derivedRepresents_mapDerivedCategoryCompIso_symm_trans e).comp
      (Functor.derivedRepresents_mapDerivedCategoryCompIso F L)
  have hτ := (Functor.derivedRepresents_associator (ofMap (mapOfNatIso e)) (ofMap (forget G))
    (ofMap G)).comp ((hσG.whiskerLeft (ofMap (mapOfNatIso e))).comp hκ)
  have hσ := ((hκ.whiskerRight (ofMap G)).comp
      (Functor.derivedRepresents_associator (ofMap (forget F)) (ofMap L) (ofMap G))).comp
    (((he.whiskerLeft (ofMap (forget F))).comp
      (Functor.derivedRepresents_associator_inv (ofMap (forget F)) (ofMap F) (ofMap L))).comp
      (hσF.whiskerRight (ofMap L)))
  have hτσ : (Functor.associator (mapOfNatIso e) (forget G) G).hom ≫
      Functor.whiskerLeft (mapOfNatIso e) (strNatIso G).hom ≫
        ((mapOfNatIsoCompForgetIso e).hom ≫ 𝟙 _) =
      (Functor.whiskerRight ((mapOfNatIsoCompForgetIso e).hom ≫ 𝟙 _) G ≫
        (Functor.associator (forget F) L G).hom) ≫
        ((Functor.whiskerLeft (forget F) (e.hom ≫ 𝟙 _) ≫
          (Functor.associator (forget F) F L).inv) ≫
          Functor.whiskerRight (strNatIso F).hom L) := by
    ext K
    simp [mapOfNatIsoCompForgetIso, mapOfNatIso_obj_str]
  have h := Functor.DerivedRepresents.ext' hτ (hσ.congr rfl hτσ.symm)
  have hM := NatTrans.congr_app h M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc] at hM
  exact hM

/-- The compatibility `derivedStrIso_hom_app_comp_derivedExactForgetCommIso` as an equivariance:
the comparison `D(U_G) (D(T) M) ≅ D(L) (D(U_F) M)` is equivariant for the derived structure of
`D(T) M` and the transport along `D(L)` of the derived structure of `M`. -/
lemma isWeilEquivariant_derivedExactForgetCommIso_hom_app (M : DerivedCategory (IsoAlgebra F)) :
    IsWeilEquivariant G.mapDerivedCategory
      ((derivedStrIso G).hom.app ((mapOfNatIso e).mapDerivedCategory.obj M))
      (transportWeilDatum L.mapDerivedCategory (derivedExactCommIso e).symm
        ((derivedStrIso F).hom.app M))
      ((derivedExactForgetCommIso e).hom.app M) := by
  unfold IsWeilEquivariant transportWeilDatum
  rw [Iso.symm_inv]
  exact (derivedStrIso_hom_app_comp_derivedExactForgetCommIso e M).symm

end CategoryTheory.Endofunctor.IsoAlgebra
