/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownCanonicalScalarCube
import all WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperCoefficientTensorUnit
import WeilConjectures.CategoryTheory.Adjunction.MateCube

/-! # Invertibility of the proper Brown scalar mate

Source: Zheng, Constructions 4.1 and 5.14--5.15 and Lemma 5.16;
Stacks 0F0G, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- The proper geometric mate used by the Brown projection is invertible.
Source: Zheng, Lemma 5.16; Stacks 0F0G and 07A4.
(blueprint: lem-pur-etale-brown-proper-scalar-mate-is-iso).

The proof is the finite-coefficient proper projection argument after restriction to
ordinary scalars. The normalized direct-image comparison and scalar pullback mate
are isomorphisms; the finite proper projection formula makes the remaining scalar
mate invertible, and exact restriction of scalars reflects isomorphisms. -/
theorem etaleBrownProperScalarMate_isIso
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) [IsProper g]
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ n, StrictEtaleBrownImageRealization O t g n A (B.level n) RV RW)
    {m n : ℕ} (h : m ≤ n) [Finite (strictEtaleBrownRing O t n)] :
    IsIso ((mateEquiv (B.level n).adjunction (B.level m).adjunction
      (.mk _ _ _ _ (B.derivedTensor h).hom))) := by
  let φ := strictEtaleBrownRingMap O t h
  let an := Etale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g
  let am := Etale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g
  let Fm := (Etale.upperStar
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g).leftDerivedFunctor
  let pn := (rg n).inverse.symm ≪≫ isoWhiskerLeft (RW.derived n)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).symm
  let pm := (rg m).inverse.symm ≪≫ isoWhiskerLeft (RW.derived m)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g).symm
  have hrep := fun k ↦ strictEtaleBrownInverse_representative O t g k A (B.level k)
    RV RW (rg k)
  have hc := strictEtaleBrownCanonicalScalarCube O t g A PW PV B RV RW rg hrep h
  rw [strictEtaleBrownCanonicalRestriction_mate] at hc
  have comm (X : DerivedCategory (strictEtaleLevel W O t n)) :
      Fm.map ((RW.scalar h).inv.app X) ≫
        pm.inv.app ((PW.scalar h).derived.obj X) ≫
        (RV.derived m).map ((B.derivedTensor h).hom.app X) =
      (Etale.scalarPullbackIso φ g).hom.app ((RW.derived n).obj X) ≫
        (Etale.scalarExtension φ V).map (pn.inv.app X) ≫
        (RV.scalar h).inv.app ((B.level n).inverse.obj X) := by
    apply (cancel_epi ((Etale.scalarPullbackIso φ g).inv.app
      ((RW.derived n).obj X))).mp
    apply (cancel_mono ((RV.derived m).map ((B.derivedTensor h).inv.app X))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact (hc X).symm
  let : (RW.derived m).IsEquivalence := RW.val.equivalence m
  let : (RV.derived m).IsEquivalence := RV.val.equivalence m
  let : (RW.derived n).IsEquivalence := RW.val.equivalence n
  let : (RV.derived n).IsEquivalence := RV.val.equivalence n
  let : IsIso (mateEquiv (B.level n).adjunction an pn.inv) :=
    isIso_mateEquiv_of_isEquivalence (B.level n).adjunction an pn.inv
  let : IsIso (mateEquiv (B.level m).adjunction am pm.inv) :=
    isIso_mateEquiv_of_isEquivalence (B.level m).adjunction am pm.inv
  let : IsIso (Etale.scalarMate φ g) :=
    (NatTrans.isIso_iff_isIso_app _).mpr (fun J ↦ Etale.proper_scalarMate_isIso φ g J)
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  have hh := mateEquiv_app_cube (B.level n).adjunction (B.level m).adjunction an am
    (B.derivedTensor h).hom (Etale.scalarPullbackIso φ g).hom
    pn.inv pm.inv (RW.scalar h).inv (RV.scalar h).inv comm K
  have hi : IsIso ((RW.scalar h).inv.app ((B.level n).direct.obj K) ≫
      (RW.derived m).map ((mateEquiv (B.level n).adjunction
        (B.level m).adjunction (B.derivedTensor h).hom).app K) ≫
      (mateEquiv (B.level m).adjunction am pm.inv).app
        ((PV.scalar h).derived.obj K)) := by
    rw [hh]
    have : IsIso ((mateEquiv an am (Etale.scalarPullbackIso φ g).hom).app
        ((RV.derived n).obj K)) := by
      change IsIso ((Etale.scalarMate φ g).app _)
      infer_instance
    infer_instance
  have : IsIso ((RW.derived m).map ((mateEquiv (B.level n).adjunction
      (B.level m).adjunction (B.derivedTensor h).hom).app K)) := by
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hi
  exact isIso_of_reflects_iso _ (RW.derived m)

end AlgebraicGeometry
