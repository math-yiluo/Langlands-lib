/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleLevelInverseTransport
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleOrdinaryInverseTransport
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.Algebra.Homology.System.SystemEvaluationKFlat
import all WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleInverseTensorCoherence
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact

/-! # Evaluation of inverse-image coefficient transport

Source: Zheng, Construction 5.15, Lemma 5.16 and Proposition 2.29(2).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

attribute [local irreducible] coefficientQuotientSheaf coefficientQuotientMap
  siteCoefficientTensorAdj

private theorem scalarInsertion_ext
    {T : Scheme.{u}} {O O' : Type (u + 1)} [CommRing O] [CommRing O']
    {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (n : ℕ)
    (M : strictEtaleLevel T O ell (index n)) (N : strictEtaleLevel T O' mu n)
    (f g : (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).obj M ⟶ N)
    (h : (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying (a.sheaf T n) M) ≫
          (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map f =
      (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying (a.sheaf T n) M) ≫
          (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map g) : f = g := by
  let adj := siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)
  let U := coefficientUnderlying (J := T.smallEtaleTopology) O ell (index n)
  let V := coefficientUnderlying (J := T.smallEtaleTopology) O' mu n
  let q := isoWhiskerRight (siteScalarUnderlyingIso (a.sheaf T n))
    (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1}))
  apply (adj.homEquiv M N).injective
  apply U.map_injective
  apply (cancel_mono (q.hom.app N)).1
  rw [transpose_underlying adj U V q M N f, transpose_underlying adj U V q M N g]
  simpa only [q, U, V, adj, coefficientUnderlying, Functor.comp_map,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    siteTensorUnitUnderlying, Functor.map_comp] using h

private theorem scalarInsertion_naturality
    {T : Scheme.{u}} {O O' : Type (u + 1)} [CommRing O] [CommRing O']
    {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (n : ℕ)
    {M N : strictEtaleLevel T O ell (index n)} (f : M ⟶ N) :
    (coefficientUnderlying (J := T.smallEtaleTopology) O ell (index n)).map f ≫
        (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying (a.sheaf T n) N) =
      (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying (a.sheaf T n) M) ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
          ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).map f) := by
  let adj := siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)
  let U := coefficientUnderlying (J := T.smallEtaleTopology) O ell (index n)
  let V := coefficientUnderlying (J := T.smallEtaleTopology) O' mu n
  let q := isoWhiskerRight (siteScalarUnderlyingIso (a.sheaf T n))
    (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1}))
  let η : U ⟶ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n) ⋙ V :=
    whiskerRight adj.unit U ≫ whiskerLeft _ q.hom
  simpa only [η, U, V, q, adj, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.comp_map,
    siteTensorUnitUnderlying, coefficientUnderlying, Functor.map_comp] using η.naturality f

section Ordinary
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (DA : ∀ n, CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    (DB : ∀ n, CoefficientDerivedImage (B.lift n).modules (B.right n) (B.levelAdj n))
    (finite : ∀ n, StrictEtaleLevelInverseTransport UT US A B DA DB n)

private theorem ordinary_evaluation
    (ordinary : US.ordinary ⋙ B.inverse ≅ A.inverse ⋙ UT.ordinary)
    (hu : ∀ n M,
      (UT.setUnit n).app (A.inverse.obj M) ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
          ((coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n).map
            (ordinary.inv.app M)) ≫
        (strictEtaleInverseUnderlying B n).hom.app (US.ordinary.obj M) =
      (strictEtaleInverseUnderlying A (index n)).hom.app M ≫
        (Scheme.etaleSetPullback g).map ((US.setUnit n).app M)) (n : ℕ) (M) :
    (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n).map
        (ordinary.inv.app M) ≫
      (B.inverseEvaluation n).hom.app (US.ordinary.obj M) ≫
      (B.lift n).modules.map ((US.val.evaluation n).hom.app M) =
    (UT.val.evaluation n).hom.app (A.inverse.obj M) ≫
      (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).map
        ((A.inverseEvaluation (index n)).hom.app M) ≫
      (finite n).ordinary.inv.app (M.level (index n)) := by
  apply (cancel_epi ((UT.val.evaluation n).inv.app (A.inverse.obj M))).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply scalarInsertion_ext a n
  apply (cancel_mono ((B.lift n).moduleUnderlying.hom.app
    ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj (M.level (index n))))).1
  simp only [Functor.map_comp, Category.assoc]
  have h := hu n M
  dsimp only [strictEtaleInverseUnderlying, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app] at h
  simp only [Category.id_comp, Category.assoc] at h
  have hut := UT.property.2.1 n (A.inverse.obj M)
  have hus := US.property.2.1 n M
  have hus' : (US.unit n).app M ≫
      (toSheaf _).map ((US.val.evaluation n).hom.app M) =
      siteTensorUnitUnderlying (a.sheaf S n) (M.level (index n)) := by
    rw [hus, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  erw [← (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map_comp_assoc,
    ← hut]
  have hn := (B.lift n).moduleUnderlying.hom.naturality ((US.val.evaluation n).hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [hn, reassoc_of% h]
  dsimp only [StrictEtaleCoefficientTransport.setUnit, Functor.whiskerRight_app]
  erw [← (Scheme.etaleSetPullback g).map_comp,
    ← (sheafCompose S.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map_comp, hus']
  have hi := scalarInsertion_naturality a n ((A.inverseEvaluation (index n)).hom.app M)
  have hu' := (finite n).unit (M.level (index n))
  have hu'' := congrArg (fun z ↦
    (coefficientUnderlying (J := T.smallEtaleTopology) O ell (index n)).map
      ((A.inverseEvaluation (index n)).hom.app M) ≫ z) hu'
  erw [← reassoc_of% hi]
  simpa only [coefficientUnderlying, coefficientEvaluation, Functor.comp_obj,
    Functor.comp_map, Category.assoc] using hu''.symm

end Ordinary

section Evaluation
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (finite : ∀ n, StrictEtaleLevelInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.level SB.openDerived.level n)
    (square : StrictEtaleInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.system SB.openDerived.system)

end Evaluation

end AlgebraicGeometry
