/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionEquivalence
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionSlices
/-! # Restriction on slices and its derived square

Source: Stacks 03A0, 03CH, 03DA, 03DG and 08J7.
(blueprint: lem-pur-native-ringed-restriction-slices). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option maxErrors 4
set_option backward.isDefEq.respectTransparency false
universe c d vc vd r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction
variable {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
  {K : GrothendieckTopology C} {J : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsEquivalence] [F.IsDenseSubsite K J]

attribute [local instance] sliceDense
variable (R : Sheaf J CommRingCat.{max c d vc vd r})
/-- Direct module restriction commutes with restriction to a slice. Both composites evaluate the
same presheaf at the same object and arrow, so the comparison is the identity natural
isomorphism.

Source: Stacks 03A0, 03CH, 03DA, 03DG and 08J7.
(blueprint: lem-pur-native-ringed-restriction-slices). -/
def sliceRestrictionIso (U : C) :
    SheafOfModules.overFunctor.{max c d vc vd r}
        (NativeRings.{max c d vc vd r, d, vd} R) (F.obj U) ⋙
      restrictModules.{max c vc, max d vd, vc, vd, r} (K := K.over U) (Over.post F) (R.over (F.obj
        U)) ≅
    restrictModules.{c, d, vc, vd, r} (K := K) F R ⋙
      SheafOfModules.overFunctor.{max c d vc vd r}
        (NativeRings.{max c d vc vd r, c, vc}
          (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)) U := by
  exact Iso.refl _

attribute [local instance] globalModulesEquivalence sliceModulesEquivalence

variable (U : C)
  [HasSheafify J AddCommGrpCat.{max c d vc vd r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
  [HasSheafify K AddCommGrpCat.{max c d vc vd r}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
  [HasSheafify (J.over (F.obj U)) AddCommGrpCat.{max c d vc vd r}]
  [(J.over (F.obj U)).WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
  [HasSheafify (K.over U) AddCommGrpCat.{max c d vc vd r}]
  [(K.over U).WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]

variable
  [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, d, vd} R)]
  [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, c, vc}
    (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R))]
  [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max d vd, vd} (R.over (F.obj U)))]
  [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
    ((restrictedCommRing.{c, d, vc, vd, r} (K := K) F R).over U))]

/-- The exact derived restriction square commutes. Both module restrictions are additive
equivalences; the two over-functors are exact. Descend their identity square to derived
categories and compose the two derived-composition comparison isomorphisms.

Source: Stacks 03A0, 03CH, 03DA, 03DG and 08J7.
(blueprint: lem-pur-native-ringed-restriction-slices). -/
def sliceDerivedRestrictionIso :
    let Tg := restrictModules.{c, d, vc, vd, r} (K := K) F R
    let Ts := restrictModules.{max c vc, max d vd, vc, vd, r}
      (K := K.over U) (Over.post F) (R.over (F.obj U))
    let A := SheafOfModules.overFunctor.{max c d vc vd r}
      (NativeRings.{max c d vc vd r, d, vd} R) (F.obj U)
    let B := SheafOfModules.overFunctor.{max c d vc vd r}
      (NativeRings.{max c d vc vd r, c, vc}
        (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)) U
    letI := (SheafOfModules.overFunctor_exact_ofUniverses.{d, vd,
      max c d vc vd r} (NativeRings.{max c d vc vd r, d, vd} R) (F.obj U)).1
    letI := (SheafOfModules.overFunctor_exact_ofUniverses.{d, vd,
      max c d vc vd r} (NativeRings.{max c d vc vd r, d, vd} R) (F.obj U)).2
    letI := (SheafOfModules.overFunctor_exact_ofUniverses.{c, vc,
      max c d vc vd r} (NativeRings.{max c d vc vd r, c, vc}
        (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)) U).1
    letI := (SheafOfModules.overFunctor_exact_ofUniverses.{c, vc,
      max c d vc vd r} (NativeRings.{max c d vc vd r, c, vc}
        (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)) U).2
    letI : HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r}
      ((NativeRings.{max c d vc vd r, d, vd} R).over (F.obj U))) := inferInstanceAs
        (HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max d vd, vd}
          (R.over (F.obj U))))
    letI : HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
      (restrictedCommRing.{max c vc, max d vd, vc, vd, r} (K := K.over U)
        (Over.post F) (R.over (F.obj U)))) := inferInstanceAs
        (HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
          ((restrictedCommRing.{c, d, vc, vd, r} (K := K) F R).over U)))
    letI : HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r}
      ((NativeRings.{max c d vc vd r, c, vc}
        (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)).over U)) := inferInstanceAs
        (HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
          ((restrictedCommRing.{c, d, vc, vd, r} (K := K) F R).over U)))
    A.mapDerivedCategory ⋙ Ts.mapDerivedCategory ≅
      Tg.mapDerivedCategory ⋙ B.mapDerivedCategory := by
  dsimp only
  letI : HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r}
      ((NativeRings.{max c d vc vd r, d, vd} R).over (F.obj U))) := inferInstanceAs
        (HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max d vd, vd}
          (R.over (F.obj U))))
  letI : HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
      (restrictedCommRing.{max c vc, max d vd, vc, vd, r} (K := K.over U)
        (Over.post F) (R.over (F.obj U)))) := inferInstanceAs
        (HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
          ((restrictedCommRing.{c, d, vc, vd, r} (K := K) F R).over U)))
  letI : HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r}
      ((NativeRings.{max c d vc vd r, c, vc}
        (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)).over U)) := inferInstanceAs
        (HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
          ((restrictedCommRing.{c, d, vc, vd, r} (K := K) F R).over U)))
  letI := globalModulesEquivalence.{c, d, vc, vd, r} (K := K) F R
  letI := sliceModulesEquivalence.{c, d, vc, vd, r} (K := K) F R U
  let Rg := NativeRings.{max c d vc vd r, d, vd} R
  let Rs := NativeRings.{max c d vc vd r, c, vc}
    (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)
  letI := (SheafOfModules.overFunctor_exact_ofUniverses.{d, vd, max c d vc vd r} Rg (F.obj U)).1
  letI := (SheafOfModules.overFunctor_exact_ofUniverses.{d, vd, max c d vc vd r} Rg (F.obj U)).2
  letI := (SheafOfModules.overFunctor_exact_ofUniverses.{c, vc, max c d vc vd r} Rs U).1
  letI := (SheafOfModules.overFunctor_exact_ofUniverses.{c, vc, max c d vc vd r} Rs U).2
  let A := SheafOfModules.overFunctor.{max c d vc vd r} Rg (F.obj U)
  let B := SheafOfModules.overFunctor.{max c d vc vd r} Rs U
  let Tg := restrictModules.{c, d, vc, vd, r} (K := K) F R
  let Ts := restrictModules.{max c vc, max d vd, vc, vd, r}
    (K := K.over U) (Over.post F) (R.over (F.obj U))
  letI : Ts.Additive := restrictModules_additive.{max c vc, max d vd, vc, vd, r}
    (K := K.over U) (Over.post F) (R.over (F.obj U))
  letI : Tg.Additive := restrictModules_additive.{c, d, vc, vd, r} (K := K) F R
  letI : A.Additive := SheafOfModules.sitePerfectOverFunctor_additive.{d, vd,
    max c d vc vd r} Rg (F.obj U)
  letI : B.Additive := SheafOfModules.sitePerfectOverFunctor_additive.{c, vc,
    max c d vc vd r} Rs U
  exact (Functor.mapDerivedCategoryCompIso A Ts) ≪≫
    Functor.mapDerivedCategoryNatIso (sliceRestrictionIso.{c, d, vc, vd, r} F R U) ≪≫
      (Functor.mapDerivedCategoryCompIso Tg B).symm

end CategoryTheory.NativeRestriction
