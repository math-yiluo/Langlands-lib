/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # Shift compatibility of the ordinary coefficient map

Source: Stacks Project, Tags 06Y6 and 08IB; an explicit shift reduction
for the tensor inheritance in Tag 0DJA(1).
(blueprint: lem-pc-tensor-coefficient-shift-homology).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

variable {A E C : Type u} [CommRing A] [CommRing E] [CommRing C]

/-- The pure-tensor coefficient maps commute with the prescribed homology shifts.
Source: Stacks Project, Tag 05G3 (extension of scalars). This is an explicit
coefficient-map compatibility for the base-change comparison of Tag 08IB, used
in the tensor inheritance of Tag 0DJA(1).

Proof: tensor induction and the two generator formulas show that tauL followed
by restriction of F_C(e) equals F_E(e) followed by tauK shifted. The termwise
extension shift maps have identity components, and restriction preserves these
identities. Thus the same square holds after those shift maps. Apply the
short-complex functor at degree i+n and then homology. The short-complex shift
isomorphism has the identity in the middle and the common factor (-1)^n at
both ends, so the square commutes after reindexing to i as well. Naturality of
mapHomologyIso for restriction moves its components through that square and
gives the displayed equality. Restriction is exact for every ring map g;
extension need not be exact. For n=0 the signs are one, and zero complexes and
zero rings present no exceptions. This uses no derived functor, model action,
or localized comparison.
(blueprint: lem-pc-tensor-coefficient-shift-homology). -/
theorem tensorCoefficient_shift_homology
    (f : A →+* E) (g : E →+* C)
    (K L : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (e : L ≅ K⟦-n⟧)
    (τK : ((extendScalars f).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((restrictScalars g).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).obj K))
    (τL : ((extendScalars f).mapHomologicalComplex (.up ℤ)).obj L ⟶
      ((restrictScalars g).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars (g.comp f)).mapHomologicalComplex (.up ℤ)).obj L))
    (hK : ∀ (j : ℤ) (a : E) (x : K.X j),
      τK.f j (a ⊗ₜ[A,f] x) = g a ⊗ₜ[A,g.comp f] x)
    (hL : ∀ (j : ℤ) (a : E) (x : L.X j),
      τL.f j (a ⊗ₜ[A,f] x) = g a ⊗ₜ[A,g.comp f] x) (i : ℤ) :
    let FE := (extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)
    let FC := (extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex (.up ℤ)
    let G := restrictScalars.{u} g
    let eE := (HomologicalComplex.homologyFunctor (ModuleCat.{u} E) (.up ℤ)
      (i + n)).mapIso (FE.mapIso e ≪≫ (FE.commShiftIso (-n)).app K) ≪≫
      (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} E) (-n) (i + n) i
        (by omega)).app (FE.obj K)
    let eC := (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ)
      (i + n)).mapIso (FC.mapIso e ≪≫ (FC.commShiftIso (-n)).app K) ≪≫
      (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} C) (-n) (i + n) i
        (by omega)).app (FC.obj K)
    HomologicalComplex.homologyMap τL (i + n) ≫
        ((FC.obj L).sc (i + n) |>.mapHomologyIso G).hom ≫ G.map eC.hom =
      eE.hom ≫ HomologicalComplex.homologyMap τK i ≫
        ((FC.obj K).sc i |>.mapHomologyIso G).hom := by
  intro FE FC G eE eC
  let GE := G.mapHomologicalComplex (.up ℤ)
  let cE := FE.mapIso e ≪≫ (FE.commShiftIso (-n)).app K
  let cC := FC.mapIso e ≪≫ (FC.commShiftIso (-n)).app K
  let cG := GE.mapIso cC ≪≫ (GE.commShiftIso (-n)).app (FC.obj K)
  have hcomplex : τL ≫ cG.hom = cE.hom ≫ τK⟦-n⟧' := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ExtendScalars.hom_ext
    intro x
    change ((extendScalars (g.comp f)).map (e.hom.f j))
      (τL.f j ((1 : E) ⊗ₜ[A,f] x)) =
      τK.f (j + -n) (((extendScalars f).map (e.hom.f j)) ((1 : E) ⊗ₜ[A,f] x))
    rw [hL, ExtendScalars.map_tmul, ExtendScalars.map_tmul, hK]
  let HE := HomologicalComplex.homologyFunctor (ModuleCat.{u} E) (.up ℤ) (i + n)
  let HC := HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) (i + n)
  let shE := (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} E)
    (-n) (i + n) i (by omega)).hom.app (FE.obj K)
  let shC := (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} C)
    (-n) (i + n) i (by omega)).hom.app (FC.obj K)
  let shG := (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} E)
    (-n) (i + n) i (by omega)).hom.app (GE.obj (FC.obj K))
  have hμ (Q : CochainComplex (ModuleCat.{u} C) ℤ) (j : ℤ) :
      (G.mapHomologicalComplexHomologyIso (.up ℤ) j).hom.app Q =
        ((Q.sc j).mapHomologyIso G).hom := by
    simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      Functor.mapHomologicalComplexHomologyIso,
      Functor.mapHomologicalComplexCompShortComplexFunctorIso, Functor.isoWhiskerRight_refl,
      ShortComplex.homologyFunctorIso, Iso.refl_trans, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, ShortComplex.homologyFunctor_obj, Functor.whiskerLeft_app,
      HomologicalComplex.homologyFunctorIso_hom_app, Functor.associator_inv_app,
      Functor.mapShortComplex_obj, Functor.associator_hom_app, NatIso.ofComponents_hom_app,
      Functor.whiskerRight_app, HomologicalComplex.homologyFunctorIso_inv_app,
      Category.id_comp]
    erw [Category.id_comp, G.map_id, Category.comp_id]
  have hshift := G.mapHomologicalComplexHomologyIso_hom_app_shiftIso
    (-n) (i + n) i (by omega) (FC.obj K)
  change HE.map ((GE.commShiftIso (-n)).inv.app (FC.obj K)) ≫
    (G.mapHomologicalComplexHomologyIso (.up ℤ) (i + n)).hom.app ((FC.obj K)⟦-n⟧) ≫
      G.map shC = shG ≫
        (G.mapHomologicalComplexHomologyIso (.up ℤ) i).hom.app (FC.obj K) at hshift
  have hshift' : (G.mapHomologicalComplexHomologyIso (.up ℤ) (i + n)).hom.app
        ((FC.obj K)⟦-n⟧) ≫ G.map shC =
      HE.map ((GE.commShiftIso (-n)).hom.app (FC.obj K)) ≫ shG ≫
        (G.mapHomologicalComplexHomologyIso (.up ℤ) i).hom.app (FC.obj K) := by
    rw [← hshift]
    simp only [← Category.assoc, ← HE.map_comp, Iso.hom_inv_id_app, HE.map_id,
      Category.id_comp]
  have hnat := (G.mapHomologicalComplexHomologyIso (.up ℤ) (i + n)).hom.naturality cC.hom
  have hshiftτ := (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} E)
    (-n) (i + n) i (by omega)).hom.naturality τK
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat hshiftτ
  change HE.map (τK⟦-n⟧') ≫ shG = shE ≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} E) (.up ℤ) i).map τK at hshiftτ
  rw [← hμ, ← hμ]
  change HE.map τL ≫ (G.mapHomologicalComplexHomologyIso (.up ℤ) (i + n)).hom.app
      (FC.obj L) ≫ G.map (HC.map cC.hom ≫ shC) =
    (HE.map cE.hom ≫ shE) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} E) (.up ℤ) i).map τK ≫
      (G.mapHomologicalComplexHomologyIso (.up ℤ) i).hom.app (FC.obj K)
  rw [G.map_comp, ← Category.assoc _ _ (G.map shC), ← hnat]
  simp only [Category.assoc]
  rw [hshift']
  rw [← Category.assoc (HE.map (GE.map cC.hom)), ← HE.map_comp]
  change HE.map τL ≫ HE.map cG.hom ≫ shG ≫ _ = _
  rw [← Category.assoc, ← HE.map_comp, hcomplex, HE.map_comp, Category.assoc]
  rw [reassoc_of% hshiftτ]

end ModuleCat
