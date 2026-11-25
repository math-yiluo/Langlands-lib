/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-! # Module and abelian stalk exchange comparison

Source: Stacks Project, Tags 03FD, 0736 and 07A7.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

/-- Forgetting module coefficients commutes with the stalk of the derived exchange.
This comparison concerns an arbitrary cartesian square and an arbitrary geometric
point of its lower-left scheme; it does not identify either side with total-space
cohomology and requires no strict-local hypothesis.

Source: Stacks Project, Tag 03FD (module/abelian acyclic comparison), together
with the termwise mate construction of Tag 0736 and Remark 07A7.
(blueprint: lem-weil-pbc-module-abelian-stalk-exchange)

Proof: Use the canonical derived direct-image coefficient comparison. Its
invertibility is proved by identifying injective module sheaves with modules
on the constant ringed site, applying injective Cech acyclicity and the Cech
vanishing criterion to every etale object, and using the sheafification of
higher direct images. Lift the proved canonical inverse-image comparison to
D+ and compose edge comparisons to obtain source and target isomorphisms.
The derived coefficient exchange compatibility identifies the maps under
these particular isomorphisms. Naturality transports this equality through
the exact forgetful functor's comparison with the single complex F[0]. Apply
homology and use naturality of the exact-functor homology isomorphism to
obtain a commuting square of abelian sheaves. Apply the abelian stalk functor
and use the inverse of Point.sheafFiberCompIso for coefficient forgetting.
Naturality gives a commuting square of stalk maps, whose two isomorphisms
yield b1 and b2 as additive equivalences. Finally,
baseChange_eq_derivedBaseChangeMapPlus identifies the module exchange with
the map used in the statement. No preservation of injectives by forgetting
and no exactness of the stalk functor is required. -/
theorem Etale.exists_addEquiv_module_abelian_stalk_exchange
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y')
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    let G := (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let S := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
        D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)
    let T := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
        R+((f')_*[AddCommGrpCat.{u + 1}])).obj K)
    let e := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
    ∃ (b₁ : (((pointSmallEtale t).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ g f q).obj F)) ≃+
        (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj S))
      (b₂ : (((pointSmallEtale t).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F)) ≃+
        (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj T)),
      ∀ x, b₂ ((((pointSmallEtale t).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        ((((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).map e).hom (b₁ x)) := by
  let U := Etale.moduleAbelianForget Λ Y'
  let V := Etale.moduleAbelianForget Λ X
  let KM := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let SM := (R+((f)_*[ModuleCat.{u + 1} Λ]) ⋙
    D+((g)^*[ModuleCat.{u + 1} Λ])).obj KM
  let TM := (D+((g')^*[ModuleCat.{u + 1} Λ]) ⋙
    R+((f')_*[ModuleCat.{u + 1} Λ])).obj KM
  let HM := DerivedCategory.Plus.homologyFunctor
    (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
  let HA := DerivedCategory.Plus.homologyFunctor
    (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
  let d := (V.mapDerivedCategoryPlusSingleFunctor 0).app F
  let s := Etale.moduleAbelianDerivedExchangeSourceIso Λ f g KM ≪≫
    (R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g)^*[AddCommGrpCat.{u + 1}])).mapIso d
  let r := Etale.moduleAbelianDerivedExchangeTargetIso Λ g' f' KM ≪≫
    (D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f')_*[AddCommGrpCat.{u + 1}])).mapIso d
  let a := (U.mapDerivedCategoryPlusHomologyFunctorIso (q : ℤ)).app SM ≪≫ HA.mapIso s
  let b := (U.mapDerivedCategoryPlusHomologyFunctorIso (q : ℤ)).app TM ≪≫ HA.mapIso r
  let em := (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app KM
  let ea := (Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (V.obj F))
  have hder : D+(U).map em ≫ r.hom = s.hom ≫ ea := by
    dsimp only [r, s, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, Etale.moduleAbelianDerivedExchange_compatibility,
      Category.assoc]
    rw [← (Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).naturality]
    simp only [ea, Category.assoc, Functor.comp_obj]
  have hsheaf : U.map (HM.map em) ≫ b.hom = a.hom ≫ HA.map ea := by
    dsimp only [a, b, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc]
    have hn := (U.mapDerivedCategoryPlusHomologyFunctorIso (q : ℤ)).hom.naturality em
    change U.map (HM.map em) ≫
        ((U.mapDerivedCategoryPlusHomologyFunctorIso (q : ℤ)).app TM).hom =
      ((U.mapDerivedCategoryPlusHomologyFunctorIso (q : ℤ)).app SM).hom ≫
        HA.map (D+(U).map em) at hn
    rw [hn]
    rw [Category.assoc, ← HA.map_comp, hder, HA.map_comp]
    simp only [Category.assoc]
  have : LocallySmall.{u} Y'.Etale := CategoryTheory.locallySmall_self _
  let P := (pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})
  let PM := (pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)
  let W : ModuleCat.{u + 1} Λ ⥤ AddCommGrpCat.{u + 1} :=
    forget₂.{u + 1, u + 1, u + 2, u + 1, u + 1, u + 2, u + 1} _ _
  have : W.IsLeftAdjoint := by
    change (ModuleCat.restrictScalars (Int.castRingHom Λ) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
    have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom Λ)).isLeftAdjoint
    infer_instance
  have : PreservesColimitsOfSize.{u, u} W :=
    (Adjunction.ofIsLeftAdjoint W).leftAdjoint_preservesColimits
  let c : U ⋙ P ≅ PM ⋙ W :=
    (pointSmallEtale t).sheafFiberCompIso W
  let i₁ := c.symm.app (HM.obj SM) ≪≫ P.mapIso a
  let i₂ := c.symm.app (HM.obj TM) ≪≫ P.mapIso b
  refine ⟨i₁.addCommGroupIsoToAddEquiv, i₂.addCommGroupIsoToAddEquiv, ?_⟩
  intro x
  have hstalk :
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          (((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
            (HM.map em)) ≫ i₂.hom = i₁.hom ≫ P.map (HA.map ea) := by
    dsimp only [i₁, i₂, Iso.trans_hom, Functor.mapIso_hom]
    have hn := c.inv.naturality (HM.map em)
    change W.map (PM.map (HM.map em)) ≫ (c.symm.app (HM.obj TM)).hom =
      (c.symm.app (HM.obj SM)).hom ≫ P.map (U.map (HM.map em)) at hn
    rw [← Category.assoc, hn]
    rw [Category.assoc, ← P.map_comp, hsheaf, P.map_comp, Category.assoc]
  have h := congrArg (fun k => k.hom x) hstalk
  simp only [Etale.baseChangeHomologyMap, Etale.baseChangeHomologyNatTrans,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Etale.baseChange_eq_derivedBaseChangeMapPlus]
  change i₂.hom.hom ((PM.map (HM.map em)).hom x) =
    (P.map (HA.map ea)).hom (i₁.hom.hom x)
  exact h

end AlgebraicGeometry
