/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs

/-! # The ordinary open/scalar conjugation identity on cochain complexes. -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
open scoped CategoryTheory.Functor CategoryTheory.TwoSquare
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

private theorem uniq_conjugate
    {C D : Type*} [Category C] [Category D]
    {L M : C ⥤ D} {R S : D ⥤ C} (a : L ⊣ R) (b : M ⊣ S) (e : S ≅ R) :
    conjugateEquiv b a (a.leftAdjointUniq (b.ofNatIsoRight e)).hom = e.hom := by
  have h : a.leftAdjointUniq (b.ofNatIsoRight e) =
      (conjugateIsoEquiv b a).symm e := by
    ext X
    simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]
  rw [h]
  change ((conjugateIsoEquiv b a) ((conjugateIsoEquiv b a).symm e)).hom = e.hom
  rw [Equiv.apply_symm_apply]

private theorem complex_conjugate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive F]
    {L : C ⥤ D} {R : D ⥤ C} {M : D ⥤ F} {S : F ⥤ D}
    {N : C ⥤ E} {T : E ⥤ C} {O : E ⥤ F} {V : F ⥤ E}
    [L.Additive] [R.Additive] [M.Additive] [S.Additive]
    [N.Additive] [T.Additive] [O.Additive] [V.Additive]
    (a : L ⊣ R) (b : M ⊣ S) (c : N ⊣ T) (d : O ⊣ V)
    (q : L ⋙ M ≅ N ⋙ O) (e : V ⋙ T ≅ S ⋙ R)
    (hq : conjugateEquiv (c.comp d) (a.comp b) q.hom = e.hom) :
    conjugateEquiv
      ((c.mapHomologicalComplex (.up ℤ)).comp (d.mapHomologicalComplex (.up ℤ)))
      ((a.mapHomologicalComplex (.up ℤ)).comp (b.mapHomologicalComplex (.up ℤ)))
      (Functor.mapHomologicalComplexCompIso q (.up ℤ)).hom =
      (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom := by
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro n
  have h := congrArg (fun t ↦ t.app (P.X n)) hq
  simpa only [conjugateEquiv_apply_app, Adjunction.comp_unit_app,
    Adjunction.comp_counit_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, Functor.comp_map,
    Functor.mapHomologicalComplex_obj_X, Functor.comp_obj] using h

/-- The cochain comparison of open extension and scalar extension is conjugate to the
cochain restriction comparison.
Source: Stacks 0E8I, 03DI; normalization proof step 2.

Proof: Uniqueness of left adjoints makes the ordinary comparison conjugate to the given
right-adjoint isomorphism. The cochain adjunction's unit and counit are the ordinary unit
and counit in every degree. Evaluate the conjugation formula in every degree and apply
that ordinary conjugation identity. This uses no flatness or nonemptiness hypotheses.
(blueprint: lem-coef-etale-open-cochain-conjugate). -/
theorem etaleOpenScalarCochainConjugate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    conjugateEquiv
      (((ProEtale.etaleSheafExtendScalarsAdjunction φ U).mapHomologicalComplex (.up ℤ)).comp
        ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) j).mapHomologicalComplex (.up ℤ)))
      (((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).comp
          ((ProEtale.etaleSheafExtendScalarsAdjunction φ X).mapHomologicalComplex (.up ℤ)))
      (Functor.mapHomologicalComplexCompIso (openScalarExtensionZero φ j) (.up ℤ)).hom =
    (Functor.mapHomologicalComplexCompIso (openRestrictScalarsIso φ j) (.up ℤ)).hom := by
  exact complex_conjugate _ _ _ _ (openScalarExtensionZero φ j)
    (openRestrictScalarsIso φ j) (uniq_conjugate _ _ _)

end AlgebraicGeometry.Etale
