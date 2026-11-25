/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.DiagonalIntegralUnitEpi

/-! # Morphisms from closed direct images of the integer sheaf

Source: Milne, Section 9, p. 67, exact sequence (*).
(blueprint: lem-sp-closed-integral-hom-ext).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Morphisms from a closed direct image of the integer sheaf agree if they agree on
constant integer generators on all pulled-back charts.
Source: Milne, Section 9, p. 67, exact sequence (*), and the sheafification adjunction.
(blueprint: lem-sp-closed-integral-hom-ext).

Proof: the ambient integer sheaf maps epimorphically onto the closed direct image.
Cancel that map. By the sheafification universal property, equality of the resulting
maps from the ambient constant sheaf is equality on the constant presheaf. The
canonical direct-image map sends each integer generator to the same integer on the
pulled-back chart, so the assumed equality gives the required presheaf equality.
This also covers empty schemes and charts. -/
theorem closedIntegral_hom_ext {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {N : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}}
    {q q' : (lowerStar AddCommGrpCat.{u + 1} i).obj
      ((constantSheaf (ProEt.topology Z) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ N}
    (h : ∀ (U : X.ProEtᵒᵖ) (k : ULift.{u + 1} ℤ),
      q.hom.app U ((toSheafify (ProEt.topology Z)
        ((Functor.const Z.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
          ((proEtaleBaseChange i).op.obj U) k) =
      q'.hom.app U ((toSheafify (ProEt.topology Z)
        ((Functor.const Z.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
          ((proEtaleBaseChange i).op.obj U) k)) : q = q' := by
  have := closedIntegralUnit_epi i
  let r := proEtaleConstantDirectImageMap i
    AddCommGrpCat.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  apply (cancel_epi r).1
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _ N.property
  have hunit := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology X) AddCommGrpCat.{u + 1}).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((lowerStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf (ProEt.topology Z) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))
    (Functor.whiskerLeft (proEtaleBaseChange i).op
      (toSheafify (ProEt.topology Z)
        ((Functor.const Z.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))
  change toSheafify (ProEt.topology X) _ ≫ r.hom = _ at hunit
  change toSheafify (ProEt.topology X) _ ≫ r.hom ≫ q.hom =
    toSheafify (ProEt.topology X) _ ≫ r.hom ≫ q'.hom
  apply Eq.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun t ↦ t ≫ q.hom) hunit))
  apply Eq.trans ?_ ((congrArg (fun t ↦ t ≫ q'.hom) hunit).symm.trans
    (Category.assoc _ _ _))
  ext U k
  exact h U k

end AlgebraicGeometry.ProEtale.SpTowerClasses
