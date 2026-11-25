/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarTensorOrdinaryPullback
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarMateOrdinaryComplexRoute
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarMateRestrictionCounitRoute

/-! # The scalar mate in ordinary tensor coordinates

Source: Stacks Project, Tags 03EK, 06YY, 07A4 and 07A6.
(blueprint: lem-sfb-scalar-mate-ordinary-tensor-route).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.DerivedScalarMate
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftAdjoint
  proEtaleRingModulePullback
  SheafOfModules.monoidalCategory ordinaryComplexIso ordinaryTensorIso
  proEtaleRingRestrictionDerivedPullback
set_option backward.defeqAttrib.useBackward true

private theorem double_mate_isIso
    {AY BY AX BX : Type*} [Category AY] [Category BY] [Category AX] [Category BX]
    {TY : AY ⥤ BY} {rY : BY ⥤ AY} {TX : AX ⥤ BX} {rX : BX ⥤ AX}
    {pA : AY ⥤ AX} {uA : AX ⥤ AY} {pB : BY ⥤ BX} {uB : BX ⥤ BY}
    (aY : TY ⊣ rY) (aX : TX ⊣ rX) (gA : pA ⊣ uA) (gB : pB ⊣ uB)
    (s : uB ⋙ rY ≅ rX ⋙ uA) :
    IsIso (((mateEquiv aY aX).symm
      ((mateEquiv gB gA).symm (TwoSquare.mk _ _ _ _ s.hom)))) := by
  rw [iterated_mateEquiv_conjugateEquiv_symm]
  change IsIso ((conjugateEquiv (aY.comp gB) (gA.comp aX)).symm s.hom)
  infer_instance

private def ordinaryScalarIso {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :
    proEtaleRingExtension a ⋙ proEtaleRingModulePullback f B (inverseRing f B) (Iso.refl _) ≅
      proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _) ⋙
        proEtaleRingExtension (inverseMap f a) := by
  let b := proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
    a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)
  let theta := ((mateEquiv (proEtaleRingExtensionAdjunction a)
    (proEtaleRingExtensionAdjunction (inverseMap f a))).symm
      (TwoSquare.mk _ _ _ _ b))
  have : IsIso theta := by
    have h := double_mate_isIso (proEtaleRingExtensionAdjunction a)
      (proEtaleRingExtensionAdjunction (inverseMap f a))
      (proEtaleRingModuleAdjunction f A (inverseRing f A) (Iso.refl _))
      (proEtaleRingModuleAdjunction f B (inverseRing f B) (Iso.refl _))
      (proEtaleRingRestrictionDirectImage f A B (inverseRing f A) (inverseRing f B)
        a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp))
    have hb := restrictionPullback_mate f A B (inverseRing f A) (inverseRing f B)
      a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)
    have he := (mateEquiv
      (proEtaleRingModuleAdjunction f B (inverseRing f B) (Iso.refl _))
      (proEtaleRingModuleAdjunction f A (inverseRing f A) (Iso.refl _))).symm_apply_apply
        (TwoSquare.mk _ _ _ _ b)
    rw [show (mateEquiv
      (proEtaleRingModuleAdjunction f B (inverseRing f B) (Iso.refl _))
      (proEtaleRingModuleAdjunction f A (inverseRing f A) (Iso.refl _)))
        (TwoSquare.mk _ _ _ _ b) = TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionDirectImage f A B (inverseRing f A) (inverseRing f B)
            a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).hom from
      by
        refine NatTrans.ext (funext fun M ↦ ?_)
        exact congr_app hb M] at he
    dsimp only [theta]
    rw [← he]
    exact h
  exact (asIso theta).symm

attribute [local irreducible] ordinaryScalarIso

private theorem ordinaryScalarIso_unit {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (M : proEtaleRingModules T A) :
    (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).map
        ((proEtaleRingExtensionAdjunction a).unit.app M) ≫
      (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
        a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).app
          ((proEtaleRingExtension a).obj M) ≫
      (restriction (inverseMap f a)).map ((ordinaryScalarIso f a).hom.app M) =
    (proEtaleRingExtensionAdjunction (inverseMap f a)).unit.app
      ((proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)).obj M) := by
  have h := unit_mateEquiv_symm (proEtaleRingExtensionAdjunction a)
    (proEtaleRingExtensionAdjunction (inverseMap f a))
    (TwoSquare.mk _ _ _ _
      (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
        a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp))) M
  apply (cancel_mono ((restriction (inverseMap f a)).map
    ((ordinaryScalarIso f a).inv.app M))).mp
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hi : (ordinaryScalarIso f a).inv =
      (((mateEquiv (proEtaleRingExtensionAdjunction a)
        (proEtaleRingExtensionAdjunction (inverseMap f a))).symm
        (TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
            a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp))))) := by
    unfold ordinaryScalarIso
    rfl
  rw [hi]
  exact h

/-- The scalar mate computes the ordinary scalar/tensor route on a K-flat complex.
This assertion involves no derived tensor presentation or geometric tensor comparison.

Source: Stacks 03EK, 06YY, 07A6, the balanced scalar route before tensor descent
(blueprint: lem-sfb-scalar-mate-ordinary-tensor-route).

Proof: take the ordinary inverse scalar-adjunction mate of the restriction
square. The derived scalar-adjunction unit normalization identifies its
localization with scalarPullback.inv after the universal counits. Restriction
of this equality is the exact restriction square on complexes. The ordinary
extension/tensor identification sends b tensor p to p tensor b. Under inverse
image its composite with the ordinary mate sends every local pure tensor to
pullback(p) tensor pullback(b). The ordinary tensor pullback followed by the
unit-normalized coefficient map has the same formula, for arbitrary local b.
The inverse-image adjunction and the balanced tensor universal property give
equality of sheaf maps. Apply the equality in each degree and sum the total
complex, using the standard bifunctor comparison with a single coefficient.
Localize and apply naturality of the exact restriction factors. This yields
the displayed scalar-counit equation. No
flatness of B or boundedness of P is used. -/
theorem scalarMate_ordinary_tensor_route
    {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (P : CochainComplex (proEtaleRingModules T A) ℤ)
    (hp : proEtaleFlatRepresentatives T A P) :
    (proEtaleRingRestrictionDerivedPullback f A B (inverseRing f A) (inverseRing f B)
        a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).inv.app
          ((proEtaleRingDerivedExtension a).obj (DerivedCategory.Q.obj P)) ≫
      (restriction (inverseMap f a)).mapDerivedCategory.map
        ((scalarPullback f a).hom.app (DerivedCategory.Q.obj P)) ≫
      (restriction (inverseMap f a)).mapDerivedCategory.map
        ((proEtaleRingDerivedExtension (inverseMap f a)).map
          ((proEtaleRingDerivedPullbackFactors f A (inverseRing f A) (Iso.refl _)).hom.app P)) ≫
      tensorScalarCounit (inverseMap f a)
        (((proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)
          ).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (ordinaryComplexIso (inverseMap f a)
        (((proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)
          ).mapHomologicalComplex (.up ℤ)).obj P)).hom =
    (pull f A).map (tensorScalarCounit a P) ≫
      (pull f A).map (DerivedCategory.Q.map (ordinaryComplexIso a P).hom) ≫
      (proEtaleRingDerivedPullbackFactors f A (inverseRing f A) (Iso.refl _)).hom.app
        (CochainComplex.mapBifunctor P (coefficientComplex a) (proEtaleOrdinaryTensor T A)) ≫
      DerivedCategory.Q.map (tensorScalarOrdinaryPullback f a P) := by
  have h := congrArg (fun k ↦ k ≫ DerivedCategory.Q.map
    (ordinaryComplexIso (inverseMap f a)
      (((proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)
        ).mapHomologicalComplex (.up ℤ)).obj P)).hom)
    (scalarMate_restriction_counit_route f a (ordinaryScalarIso f a)
      (ordinaryScalarIso_unit f a) P hp)
  simp only [Category.assoc] at h
  rw [← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp] at h
  simp only [Category.assoc] at h
  erw [scalarMate_ordinary_complex_route f a (ordinaryScalarIso f a)
    (ordinaryScalarIso_unit f a) P, DerivedCategory.Q.map_comp] at h
  rw [← reassoc_of% ((proEtaleRingDerivedPullbackFactors f A (inverseRing f A)
    (Iso.refl _)).hom.naturality (ordinaryComplexIso a P).hom)] at h
  exact h

end AlgebraicGeometry.Scheme.DerivedScalarMate
