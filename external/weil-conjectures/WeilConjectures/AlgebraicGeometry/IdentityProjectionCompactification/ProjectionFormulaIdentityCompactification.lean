/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectPackageOnSiteSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionFormulaCompactified

/-!
# Identity compactification and the projection formula

Source: Weil conjectures blueprint, proper base change, order 1272, identity
compactification lemma; detailed proper_base_change.tex, lines 5600--5616
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification).

We use the normalized presentation of the identity open immersion: its extension
by zero and its restriction are the identity functor, with identity unit and counit.
Thus the definition Rp_* j_! is the actual composite (identity functor) followed by
Rp_*, and the open tensor comparison and composition constraint are identities.
These definitions describe this specific compactification, not arbitrary shriek data.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdentityProjectionCompactification

private def identitySheafPushforward (X : Scheme.{u}) :
    proEtaleSheafDirectImage (𝟙 X) CommRingCat.{u + 1} ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) X)
    CommRingCat.{u + 1} (ProEt.topology X)

private def identityCoefficients (X : Scheme.{u})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).obj S ≅ S :=
  ((conjugateIsoEquiv Adjunction.id
    (proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1})).symm
      (identitySheafPushforward X).symm).app S

private theorem identityCoefficientUnit (X : Scheme.{u})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    proEtaleRingDirectImageMap (𝟙 X) S S (identityCoefficients X S) =
      (identitySheafPushforward X).inv.app S := by
  exact (unit_conjugateEquiv_symm Adjunction.id
    (proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1})
    (identitySheafPushforward X).inv S).symm

private def identityModulePushforward (X : Scheme.{u})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    proEtaleRingModuleDirectImage (𝟙 X) S S (identityCoefficients X S) ≅ 𝟭 _ := by
  letI : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ X)).IsContinuous
      (ProEt.topology X) (ProEt.topology X) := Functor.isContinuous_id _
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let e := MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) X
  let t : A ⟶ ((proEtaleBaseChange (𝟙 X)).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology X) (ProEt.topology X)).obj A :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap (𝟙 X) S S (identityCoefficients X S)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have ht : t ≫ (Functor.sheafPushforwardContinuousNatTrans e.inv _ _ _).app A = 𝟙 A := by
    dsimp only [t]
    rw [identityCoefficientUnit]
    ext U x
    change (S.obj.map (e.hom.app U.unop).op ≫ S.obj.map (e.inv.app U.unop).op) x = x
    rw [← S.obj.map_comp, ← CategoryTheory.op_comp, Iso.inv_hom_id_app, CategoryTheory.op_id,
      S.obj.map_id]
    rfl
  exact SheafOfModules.pushforwardCongr₂ (φ := t) e.symm ht ≪≫
    SheafOfModules.pushforwardId A

private def identityDerivedPullback (X : Scheme.{u})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    proEtaleRingDerivedPullback (𝟙 X) S S (identityCoefficients X S) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
    ((proEtaleRingModuleAdjunction (𝟙 X) S S (identityCoefficients X S)).leftAdjointIdIso
      (identityModulePushforward X S)) ≪≫ Functor.mapDerivedCategoryIdIso _

private def identityDerivedOpenExtension (X : Scheme.{u})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    proEtaleRingDerivedOpenExtension (𝟙 X) S S (identityCoefficients X S) ≅ 𝟭 _ :=
  (proEtaleRingDerivedOpenAdjunction (𝟙 X) S S (identityCoefficients X S)).leftAdjointIdIso
    (identityDerivedPullback X S)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
  (aY : ProEtaleTensorModel Y R) (aX : ProEtaleTensorModel X S)
  (E : DerivedCategory (proEtaleRingModules X S))
  (Q : DerivedCategory (proEtaleRingModules Y R))

/-- Rp_* j_! for j=1_X, with the normalized exact identity extension by zero.
Source: blueprint order 1272
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification). -/
abbrev directImage := 𝟭 _ ⋙ proEtaleRingDerivedDirectImage f R S c

/-- The open-piece tensor and composite-pullback identifications for the identity open.
Source: blueprint order 1272
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification). -/
def theta := 𝟙 (aX.tensor.obj (E, (proEtaleRingDerivedPullback f R S c).obj Q))

/-- The ordered compactification composite, with its actual final Rp_* theta arrow.
Source: blueprint orders 1271--1272
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification). -/
def forward :
    aY.tensor.obj ((directImage f R S c).obj E, Q) ⟶
      (directImage f R S c).obj
        (aX.tensor.obj (E, (proEtaleRingDerivedPullback f R S c).obj Q)) :=
  proEtaleProjectionFormulaMate f R S c aY aX E Q ≫
    (proEtaleRingDerivedDirectImage f R S c).map (theta f R S c aX E Q)

/-- The canonical mate is invertible at the perfect coefficient used in the formula.
Source: blueprint orders 1271--1272
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification).
Proof: specialize the compactified perfect projection formula to (1_X,f).
The identity open-piece comparison and composite-pullback constraint are identities;
its ordered composite is the projection mate. Its invertibility is therefore exactly
that supplied by the compactified formula. No boundedness of E or global bound for Q
is used. -/
theorem mate_isIso [IsProper f] (hQ : SheafOfModules.IsPerfectOnSmallRingedSite R Q) :
    IsIso (proEtaleProjectionFormulaMate f R S c aY aX E Q) := by
  let ci := identityCoefficients X S
  let d := Compactification.ofIsProper f
  let : QuasiCompact d.i := inferInstanceAs (QuasiCompact (𝟙 X))
  let e := (identityDerivedOpenExtension X S).app E
  obtain ⟨hα, hπ, _⟩ := proEtaleProjectionFormula_compactified
    d R S S c ci aY aX aX E Q hQ
  have : IsIso (derivedProjectionFormulaMate
      (proEtaleRingDerivedPullback f R S c) (proEtaleRingDerivedDirectImage f R S c)
      (proEtaleRingDerivedAdjunction f R S c) aY.tensor aX.tensor
      (proEtaleCanonicalTensorComparison f R S c aY aX)
      ((proEtaleRingDerivedOpenExtension (𝟙 X) S S ci).obj E) Q) := hπ
  have hn := derivedProjectionFormulaMate_naturality
    (proEtaleRingDerivedPullback f R S c) (proEtaleRingDerivedDirectImage f R S c)
    (proEtaleRingDerivedAdjunction f R S c) aY.tensor aX.tensor
    (proEtaleCanonicalTensorComparison f R S c aY aX) _ E Q e.hom
  have : IsIso (Prod.mkHom e.hom
      (𝟙 ((proEtaleRingDerivedPullback f R S c).obj Q))) :=
    (Iso.prod e (Iso.refl _)).isIso_hom
  have : IsIso (Prod.mkHom
      ((proEtaleRingDerivedDirectImage f R S c).map e.hom) (𝟙 Q)) :=
    (Iso.prod ((proEtaleRingDerivedDirectImage f R S c).mapIso e) (Iso.refl Q)).isIso_hom
  have : IsIso (aY.tensor.map (Prod.mkHom
      ((proEtaleRingDerivedDirectImage f R S c).map e.hom) (𝟙 Q)) ≫
      proEtaleProjectionFormulaMate f R S c aY aX E Q) := by
    unfold proEtaleProjectionFormulaMate
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (aY.tensor.map (Prod.mkHom
      ((proEtaleRingDerivedDirectImage f R S c).map e.hom) (𝟙 Q))) _

variable [hf : IsProper f]

/-- The inverse rho of the same canonical mate, determined by its inverse identities.
Source: blueprint order 1272
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification). -/
def rho (hQ : SheafOfModules.IsPerfectOnSmallRingedSite R Q) :=
  @inv _ _ _ _ (proEtaleProjectionFormulaMate f R S c aY aX E Q)
    (mate_isIso f R S c aY aX E Q hQ)

/-- The reverse ordered compactification composite, with theta inverse followed by rho.
Source: blueprint orders 1271--1272
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification). -/
def backward (hQ : SheafOfModules.IsPerfectOnSmallRingedSite R Q) :=
  (proEtaleRingDerivedDirectImage f R S c).map
    (𝟙 (aX.tensor.obj (E, (proEtaleRingDerivedPullback f R S c).obj Q))) ≫
      rho f R S c aY aX E Q hQ

end AlgebraicGeometry.Scheme.IdentityProjectionCompactification
