/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedCoefficientImmersion.LocallyClosedModuleExtensionModel
import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedModuleExtensionAssociativityPart
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
/-! Unit portion of locally closed model coherence. -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

-- Coefficient unit equalities are mates of the sectionwise direct-image unit equalities.
private noncomputable abbrev ringAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleSheafAdjunction f CommRingCat.{u + 1}

private theorem ring_pull_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateIsoEquiv (ringAdj g) (ringAdj f)
      (eqToIso (congrArg (fun k ↦ proEtaleSheafInverseImage k CommRingCat.{u + 1}) h)) =
      (eqToIso (congrArg
        (fun k ↦ proEtaleSheafDirectImage k CommRingCat.{u + 1}) h)).symm := by
  cases h
  ext : 1
  simp

private theorem ring_pull_left_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingInverseImageComp (𝟙 X) f ≪≫
      Functor.isoWhiskerLeft (proEtaleSheafInverseImage f CommRingCat.{u + 1})
        (proEtaleRingInverseImageId X) ≪≫ Functor.rightUnitor _ =
      eqToIso (congrArg
        (fun k ↦ proEtaleSheafInverseImage k CommRingCat.{u + 1}) (Category.id_comp f)) := by
  let q := AlgebraicGeometry.ProEtale.lowerStarComp CommRingCat.{u + 1} (𝟙 X) f ≪≫
    eqToIso (congrArg
      (fun k ↦ proEtaleSheafDirectImage k CommRingCat.{u + 1}) (Category.id_comp f))
  have hq : q = Functor.isoWhiskerRight
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X)
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}) ≪≫ Functor.leftUnitor _ := by
    dsimp only [q]
    rw [AlgebraicGeometry.ProEtale.legacy_lowerStarComp_id_left]
    ext M T
    simp [AlgebraicGeometry.ProEtale.lowerStarCongr]
    rfl
  apply (conjugateIsoEquiv (ringAdj f) (ringAdj (𝟙 X ≫ f))).injective
  rw [conjugateIsoEquiv_trans _ ((ringAdj f).comp (ringAdj (𝟙 X))) _,
    conjugateIsoEquiv_trans _ ((ringAdj f).comp Adjunction.id) _,
    conjugateIsoEquiv_rightUnitor, conjugateIsoEquiv_isoWhiskerLeft,
    ring_pull_congr (Category.id_comp f)]
  simp only [proEtaleRingInverseImageComp, proEtaleRingInverseImageId,
    conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply]
  change (Functor.isoWhiskerRight
    (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X)
    (proEtaleSheafDirectImage f CommRingCat.{u + 1}) ≪≫ Functor.leftUnitor _).symm ≪≫
      AlgebraicGeometry.ProEtale.lowerStarComp CommRingCat.{u + 1} (𝟙 X) f = _
  rw [← hq]
  apply Iso.ext
  simp only [q, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme
