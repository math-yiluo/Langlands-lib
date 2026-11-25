/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarTensorOrdinaryPullback
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarMateOrdinaryModuleRoute
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.TensorScalarOrdinarySinglePullback

/-! # The ordinary scalar mate square on complexes

Source: Stacks Project, Tags 03EL and 07A4.
(blueprint: lem-sfb-scalar-mate-ordinary-complex-route).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.DerivedScalarMate
section Proof

-- Use countable colimits directly instead of diagram-wide instance search.
private theorem ordinaryTensorTotal {W : Scheme.{u}}
    (A : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (P Q : CochainComplex (proEtaleRingModules W A) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (proEtaleOrdinaryTensor W A) (.up ℤ) :=
  fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (inferInstance : HasColimitsOfSize.{0, 0} (proEtaleRingModules W A)) _ _) _

attribute [local instance] ordinaryTensorTotal
private theorem route_via_isos
    {C : Type*} [Category C] {S U V Y Y' X X' : C}
    (sY : Y' ≅ Y) (sX : X' ≅ X) (b : S ⟶ U) (c : U ⟶ V)
    (oX : V ⟶ X) (oY : S ⟶ Y) (j : Y' ⟶ X') (τ : Y ⟶ X)
    (hs : sY.inv ≫ j ≫ sX.hom = τ)
    (hm : b ≫ c ≫ oX = oY ≫ τ) :
    b ≫ c ≫ oX ≫ sX.inv = oY ≫ sY.inv ≫ j := by
  apply (cancel_mono sX.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hm, ← hs]

end Proof

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint proEtaleRingModulePullback
  proEtaleRingExtension proEtaleRingRestrictionPullbackInv
  SheafOfModules.monoidalCategory ordinaryTensorIso ordinaryComplexIso
  HomologicalComplex₂.total CategoryTheory.Functor.mapBifunctorHomologicalComplex
  CochainComplex.mapBifunctorSingle₂Iso
set_option backward.defeqAttrib.useBackward true

/-- The ordinary module scalar/tensor square remains compatible on cochain complexes.
Source: Stacks Project, Tags 03EL and 07A4
(blueprint: lem-sfb-scalar-mate-ordinary-complex-route).

Proof: identify inverse total pullback with the canonical bifunctor comparison on
homogeneous summands. The single-complex comparison and its coefficient naturality
identify its degree-zero coefficient specialization with the ordinary tensor pullback
and coefficient map in every degree. Apply the ordinary module route degreewise,
then conjugate by the single-complex isomorphisms defining ordinaryComplexIso. -/
theorem scalarMate_ordinary_complex_route {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (χ : proEtaleRingExtension a ⋙
      proEtaleRingModulePullback f B (inverseRing f B) (Iso.refl _) ≅
      proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _) ⋙
        proEtaleRingExtension (inverseMap f a))
    (hχ : ∀ M, (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).map
        ((proEtaleRingExtensionAdjunction a).unit.app M) ≫
      (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
        a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).app
          ((proEtaleRingExtension a).obj M) ≫
      (restriction (inverseMap f a)).map (χ.hom.app M) =
      (proEtaleRingExtensionAdjunction (inverseMap f a)).unit.app
        ((proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).obj M))
    (P : CochainComplex (proEtaleRingModules T A) ℤ) :
    let FA := proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)
    let rZ := restriction (inverseMap f a)
    let EP := ((proEtaleRingExtension a).mapHomologicalComplex (.up ℤ)).obj P
    (NatTrans.mapHomologicalComplex
      (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
        a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)) (.up ℤ)).app EP ≫
      (rZ.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex χ (.up ℤ)).hom.app P) ≫
      (ordinaryComplexIso (inverseMap f a) ((FA.mapHomologicalComplex (.up ℤ)).obj P)).hom =
    (FA.mapHomologicalComplex (.up ℤ)).map (ordinaryComplexIso a P).hom ≫
      tensorScalarOrdinaryPullback f a P := by
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.monoidalCategory (inverseRing f A)
  let : MonoidalPreadditive (proEtaleRingModules T A) := proEtaleTensorPreadditive T A
  let : MonoidalPreadditive (proEtaleRingModules Z (inverseRing f A)) :=
    proEtaleTensorPreadditive Z (inverseRing f A)
  let : ∀ K L : CochainComplex (proEtaleRingModules T A) ℤ,
      HomologicalComplex.HasMapBifunctor K L (proEtaleOrdinaryTensor T A) (.up ℤ) :=
    ordinaryTensorTotal A
  let : ∀ K L : CochainComplex (proEtaleRingModules Z (inverseRing f A)) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (proEtaleOrdinaryTensor Z (inverseRing f A)) (.up ℤ) :=
    ordinaryTensorTotal (inverseRing f A)
  dsimp only
  let FA := proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)
  let FAc := FA.mapHomologicalComplex (.up ℤ)
  let TZ := proEtaleOrdinaryTensor Z (inverseRing f A)
  let FP := FAc.obj P
  let rXc := (restriction (inverseMap f a)).mapHomologicalComplex (.up ℤ)
  let EP := ((proEtaleRingExtension a).mapHomologicalComplex (.up ℤ)).obj P
  let b := (NatTrans.mapHomologicalComplex
    (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
      a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)) (.up ℤ)).app EP
  let c := (NatIso.mapHomologicalComplex
    χ (.up ℤ)).hom.app P
  let : (ordinaryTensor a).Additive :=
    CategoryTheory.Functor.additive_of_iso (ordinaryTensorIso a)
  let : (ordinaryTensor (inverseMap f a)).Additive :=
    CategoryTheory.Functor.additive_of_iso (ordinaryTensorIso (inverseMap f a))
  let oX := (NatIso.mapHomologicalComplex
    (ordinaryTensorIso (inverseMap f a)) (.up ℤ)).hom.app FP
  let oY := (NatIso.mapHomologicalComplex
    (ordinaryTensorIso a) (.up ℤ)).hom.app P
  let sy := CochainComplex.mapBifunctorSingle₂Iso
    (proEtaleOrdinaryTensor T A) (coefficient a) P
  let sx := CochainComplex.mapBifunctorSingle₂Iso TZ (coefficient (inverseMap f a)) FP
  let τ := FAc.map sy.inv ≫ tensorScalarOrdinaryPullback f a P ≫ sx.hom
  have hm : b ≫ rXc.map c ≫ oX = FAc.map oY ≫ τ := by
    apply HomologicalComplex.hom_ext
    intro n
    dsimp only [b, rXc, c, oX, oY, EP, FP, FAc, FA,
      HomologicalComplex.comp_f, CategoryTheory.Functor.mapHomologicalComplex_map_f,
      NatIso.mapHomologicalComplex_hom_app_f, NatTrans.mapHomologicalComplex_app_f,
      CategoryTheory.Functor.mapHomologicalComplex_obj_X]
    have hm := scalarMate_ordinary_module_route f a χ hχ (P.X n)
    have ht := tensorScalarOrdinaryPullback_single_f f a P n
    exact hm.trans (congrArg
      (fun q ↦ FA.map ((ordinaryTensorIso a).hom.app (P.X n)) ≫ q) ht.symm)
  have h := route_via_isos
    (FAc.mapIso (CochainComplex.mapBifunctorSingle₂Iso
      (proEtaleOrdinaryTensor T A) (coefficient a) P))
    (CochainComplex.mapBifunctorSingle₂Iso TZ (coefficient (inverseMap f a)) FP)
    b (rXc.map c) oX (FAc.map oY) (tensorScalarOrdinaryPullback f a P) τ
    rfl hm
  unfold ordinaryComplexIso
  simp only [Iso.trans_hom, Iso.symm_hom]
  erw [FAc.map_comp]
  simpa only [oX, oY, CategoryTheory.Functor.mapHomologicalComplexCompIso,
    Iso.app_hom, Category.assoc, CategoryTheory.Functor.mapIso_inv] using h

end AlgebraicGeometry.Scheme.DerivedScalarMate
