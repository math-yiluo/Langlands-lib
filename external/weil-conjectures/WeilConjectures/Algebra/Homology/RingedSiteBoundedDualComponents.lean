/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.HomTensorDifferential
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniverses
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints
import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHomComplex
import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

/-! # Components of the bounded ordinary sheaf dual

Source: Stacks Project, sites-cohomology.tex, Tags 08JJ and 0A8X
(auxiliary; not a blueprint node).

The abbreviations below only expand the recorded Hom constructions and the
coefficient sheaf in degree zero. The component is the actual product projection.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe c v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteBoundedDual

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  (R : Sheaf J CommRingCat.{max c v r})

/-- Module sheaves in the chosen ambient universe.
Source: Stacks 08JJ, 0A8X (auxiliary; not a blueprint node). -/
abbrev Modules := SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

/-- The standard zero-object structure obtained from the terminal module sheaf.
Source: Stacks 0A8X (auxiliary; not a blueprint node). -/
instance modulesHasZeroObject : HasZeroObject (Modules.{c, v, r} R) :=
  hasZeroObject_of_hasTerminal_object

/-- The coefficient sheaf as a module over itself.
Source: Stacks 08JJ (auxiliary; not a blueprint node). -/
abbrev coefficient : Modules.{c, v, r} R := SheafOfModules.unit _

/-- The standard complex R[0], with the standard single-complex construction.
Source: Stacks 08JJ (auxiliary; not a blueprint node). -/
abbrev zeroComplex : CochainComplex (Modules.{c, v, r} R) ℤ :=
  (CochainComplex.singleFunctor (Modules.{c, v, r} R) 0).obj (coefficient.{c, v, r} R)

/-- The recorded internal sheaf Hom into the coefficient sheaf.
Source: Stacks 04TT, 08JJ (auxiliary; not a blueprint node). -/
abbrev dual (T : Modules.{c, v, r} R) : Modules.{c, v, r} R :=
  SheafOfModules.homObj T (coefficient.{c, v, r} R)

/-- The recorded sheaf Hom complex into R[0].
Source: Stacks 0A8X, 08JJ (auxiliary; not a blueprint node). -/
abbrev complexDual (E : CochainComplex (Modules.{c, v, r} R) ℤ) :
    CochainComplex (Modules.{c, v, r} R) ℤ :=
  homComplex (R := R) E (zeroComplex.{c, v, r} R)

/-- Projection to the sole possibly nonzero Hom factor, followed by O^0 = R.
Source: Stacks 0A8X, 08JJ (auxiliary; not a blueprint node). -/
def component (E : CochainComplex (Modules.{c, v, r} R) ℤ) (p q : ℤ) (h : p + q = 0) :
    (complexDual.{c, v, r} R E).X q ⟶ dual.{c, v, r} R (E.X p) :=
  homComplexπ E (zeroComplex.{c, v, r} R) q p 0 h ≫
    SheafOfModules.homObjMap (𝟙 (E.X p))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (coefficient.{c, v, r} R)).hom

attribute [local irreducible] homComplexFunctor homComplexπ

private lemma homMap_zero_right {A B D : Modules.{c, v, r} R} :
    SheafOfModules.homObjMap (R := R) (𝟙 A) (0 : B ⟶ D) = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  rfl

private lemma homZero_right (A B : Modules.{c, v, r} R) (hB : IsZero B) :
    IsZero (SheafOfModules.homObj (R := R) A B) := by
  rw [IsZero.iff_id_eq_zero, ← SheafOfModules.homObjMap_id,
    hB.eq_of_tgt (𝟙 B) 0, homMap_zero_right.{c, v, r}]

private lemma projection_isIso (E : CochainComplex (Modules.{c, v, r} R) ℤ)
    (p q : ℤ) (h : p + q = 0) :
    IsIso (homComplexπ E (zeroComplex.{c, v, r} R) q p 0 h) := by
  classical
  let Q := fun j : ℤ ↦ SheafOfModules.homObj (R := R)
    (E.X j) ((zeroComplex.{c, v, r} R).X (j + q))
  let hc := homComplexIsLimit E (zeroComplex.{c, v, r} R) q
  let v : Q p ⟶ (complexDual.{c, v, r} R E).X q := Fan.IsLimit.lift hc
    (fun j ↦ if hj : j = p then eqToHom (congrArg Q hj.symm) else 0)
  have hv : v ≫ homComplexπ E (zeroComplex.{c, v, r} R) q p (p + q) rfl = 𝟙 (Q p) := by
    change Fan.IsLimit.lift hc _ ≫
      (Fan.mk _ (fun j : ℤ ↦ homComplexπ E (zeroComplex.{c, v, r} R) q j (j + q) rfl)).proj p = _
    rw [Fan.IsLimit.fac]
    simp
  have hp : homComplexπ E (zeroComplex.{c, v, r} R) q p (p + q) rfl ≫ v = 𝟙 _ := by
    apply Fan.IsLimit.hom_ext hc
    intro j
    change (_ ≫ v) ≫ homComplexπ E (zeroComplex.{c, v, r} R) q j (j + q) rfl =
      𝟙 _ ≫ homComplexπ E (zeroComplex.{c, v, r} R) q j (j + q) rfl
    by_cases hj : j = p
    · subst j
      rw [Category.assoc, hv, Category.comp_id, Category.id_comp]
    · exact (homZero_right.{c, v, r} R (E.X j) ((zeroComplex.{c, v, r} R).X (j + q))
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ (j + q)
          (by omega))).eq_of_tgt _ _
  have hi := (Iso.mk _ v hp hv).isIso_hom
  have transport {t : ℤ} (ht : p + q = t) :
      IsIso (homComplexπ E (zeroComplex.{c, v, r} R) q p t ht) := by
    subst t
    exact hi
  exact transport h

private lemma component_d (E : CochainComplex (Modules.{c, v, r} R) ℤ)
    (n m p p' : ℤ) (hnm : n + 1 = m) (h : p + n = 0) (h' : p' + m = 0) :
    (complexDual.{c, v, r} R E).d n m ≫ component.{c, v, r} R E p' m h' =
      m.negOnePow • (component.{c, v, r} R E p n h ≫
        SheafOfModules.homObjMap (E.d p' p) (𝟙 (coefficient.{c, v, r} R))) := by
  unfold component
  rw [← Category.assoc, homComplex_d_π E (zeroComplex.{c, v, r} R)
    n m p' 0 (-1) p hnm h' (by omega) h]
  have hz : (zeroComplex.{c, v, r} R).d (-1) 0 = 0 := rfl
  rw [hz, homMap_zero_right.{c, v, r}, comp_zero, zero_sub]
  simp only [Preadditive.neg_comp, Linear.units_smul_comp,
    Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
    Category.id_comp, Category.comp_id, ← hnm, Int.negOnePow_succ, Units.neg_smul]

end CategoryTheory.RingedSiteBoundedDual
