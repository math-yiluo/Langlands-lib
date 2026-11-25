/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero

import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryRestrictionPullbackSquare
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.Adjunction.ConjugatePaste
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarAssociatorConjugate
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Coefficient cocycle for normalized open scalar comparisons

The equation uses the prescribed scalar associator and the prescribed comparison for
sectionwise sheafified extension by zero on the full ordinary unbounded categories.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Limits CategoryTheory.Functor

private noncomputable abbrev openAdj (A : Type u) [CommRing A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :=
  proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing Z A)
    (proEtaleConstantRing U A) (proEtaleConstantRingComparison j A)

attribute [local irreducible] proEtaleRingModulePullback
  proEtaleRingModuleAdjunction proEtaleRingDerivedOpenAdjunction

private local instance ordinaryComparisonIsIso
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) :
    IsIso (ordinaryRestrictionComparison φ j) :=
  proEtaleRingRestrictionPullbackInv_isIso _ _ _ _ _ _ _ _ _ _

private theorem normalizedCocycle
    {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [Category A₁] [Category A₂] [Category B₁] [Category B₂]
    [Category C₁] [Category C₂]
    {Oa : A₁ ⥤ A₂} {Ra : A₂ ⥤ A₁} {Ob : B₁ ⥤ B₂} {Rb : B₂ ⥤ B₁}
    {Oc : C₁ ⥤ C₂} {Rc : C₂ ⥤ C₁}
    {Su : A₁ ⥤ B₁} {Ru : B₁ ⥤ A₁} {Sz : A₂ ⥤ B₂} {Rz : B₂ ⥤ A₂}
    {Tu : B₁ ⥤ C₁} {Vu : C₁ ⥤ B₁} {Tz : B₂ ⥤ C₂} {Vz : C₂ ⥤ B₂}
    {Qu : A₁ ⥤ C₁} {Wu : C₁ ⥤ A₁} {Qz : A₂ ⥤ C₂} {Wz : C₂ ⥤ A₂}
    (a : Oa ⊣ Ra) (b : Ob ⊣ Rb) (c : Oc ⊣ Rc)
    (s : Su ⊣ Ru) (s' : Sz ⊣ Rz) (t : Tu ⊣ Vu) (t' : Tz ⊣ Vz)
    (q : Qu ⊣ Wu) (q' : Qz ⊣ Wz)
    (β : Oa ⋙ Sz ≅ Su ⋙ Ob) (γ : Ob ⋙ Tz ≅ Tu ⋙ Oc)
    (δ : Oa ⋙ Qz ≅ Qu ⋙ Oc) (α : Su ⋙ Tu ≅ Qu) (α' : Sz ⋙ Tz ≅ Qz)
    (χ : Rz ⋙ Ra ≅ Rb ⋙ Ru) (χ' : Vz ⋙ Rb ≅ Rc ⋙ Vu)
    (χ'' : Wz ⋙ Ra ≅ Rc ⋙ Wu) (ρ : Vu ⋙ Ru ≅ Wu) (ρ' : Vz ⋙ Rz ≅ Wz)
    (hβ : conjugateEquiv (a.comp s') (s.comp b) β.inv = χ.hom)
    (hγ : conjugateEquiv (b.comp t') (t.comp c) γ.inv = χ'.hom)
    (hδ : conjugateEquiv (a.comp q') (q.comp c) δ.inv = χ''.hom)
    (hα : conjugateEquiv (s.comp t) q α.inv = ρ.hom)
    (hα' : conjugateEquiv (s'.comp t') q' α'.inv = ρ'.hom)
    (h : ∀ K, χ.hom.app (Vz.obj K) ≫ Ru.map (χ'.hom.app K) ≫
      ρ.hom.app (Rc.obj K) = Ra.map (ρ'.hom.app K) ≫ χ''.hom.app K)
    (M : A₁) :
    α'.hom.app (Oa.obj M) ≫ δ.hom.app M =
      Tz.map (β.hom.app M) ≫ γ.hom.app (Su.obj M) ≫ Oc.map (α.hom.app M) := by
  have hh := conjugateEquiv_paste a b c s s' t t' q q' β.inv γ.inv δ.inv
    α.inv α'.inv (by
      rw [hβ, hγ, hδ, hα, hα']
      apply NatTrans.ext
      funext K
      exact h K)
  let e₁ := isoWhiskerLeft Oa α' ≪≫ δ
  let e₂ := isoWhiskerRight β Tz ≪≫ isoWhiskerLeft Su γ ≪≫ isoWhiskerRight α Oc
  have he : e₁ = e₂ := by
    apply Iso.ext_inv
    simpa only [e₁, e₂, Iso.trans_inv, NatTrans.comp_app, isoWhiskerLeft_inv,
      isoWhiskerRight_inv, whiskerLeft_app, whiskerRight_app, Category.assoc]
      using hh.symm
  simpa only [e₁, e₂, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Category.assoc]
    using congrArg (fun e ↦ e.hom.app M) he

end AlgebraicGeometry.ProEtale
