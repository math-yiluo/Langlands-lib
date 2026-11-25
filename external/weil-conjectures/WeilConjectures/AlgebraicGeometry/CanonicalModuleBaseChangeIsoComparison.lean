/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap

import WeilConjectures.AlgebraicGeometry.DerivedModulePullbackComparison
import WeilConjectures.AlgebraicGeometry.CanonicalModuleBaseChangeIsoComparisonCompat

/-! # Canonical module base change under changes of coordinates

Source: Stacks Project, Tags 08HY, 0D5T, and 08IB.
(blueprint: lem-pc-canonical-module-base-change-iso-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- Changing the two base coordinates by isomorphisms preserves the canonical
module base-change arrow. This statement involves no open restriction.
Source: Stacks Project, Tag 08HY, counit construction; Tag 0D5T, composition;
Tag 08IB, affine coordinate change in the first proof paragraph.
(blueprint: lem-pc-canonical-module-base-change-iso-comparison).

Proof:
1. Apply exists_isDerivedModulePullbackComparison to obtain a comparison
at the first projection of the chosen coordinate pullback. This uses the
existing derived-pullback counit, evaluated at the module in degree zero;
no transport of the original comparison is required for existence.
2. Apply canonicalModuleBaseChange_iso_comparison_ab to this comparison. It
supplies the coordinate isomorphisms and the equality. Its geometric argument
uses pullback/direct-image composition and mate naturality; its independence
of the chosen comparison uses the ordinary target-automorphism lemma.
3. Package the comparison, its property, and the two isomorphisms with the
equality. This includes empty schemes and zero modules.
-/
theorem exists_canonicalModuleBaseChange_iso_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (G : X.Modules)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (hc : IsDerivedModulePullbackComparison g' G c)
    {A B : Scheme.{u}} (eS : S ≅ A) (eT : S' ≅ B) :
    let fA := f ≫ eS.hom
    let gA := eT.inv ≫ g ≫ eS.hom
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
    let T := schemeDerivedDirectImage eT.inv
    ∃ c0 : (derivedPullback (pullback.fst fA gA)).obj E ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj G),
      IsDerivedModulePullbackComparison (pullback.fst fA gA) G c0 ∧
      ∃ a : (derivedPullback g).obj ((schemeDerivedDirectImage f).obj E) ≅
          T.obj ((derivedPullback gA).obj ((schemeDerivedDirectImage fA).obj E)),
      ∃ b : (schemeDerivedDirectImage f').obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
                ((Scheme.Modules.tensorPullback g').obj G)) ≅
          T.obj ((schemeDerivedDirectImage (pullback.snd fA gA)).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
                ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj G))),
        (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
            (schemeDerivedDirectImage f').map c) ≫ b.hom =
          a.hom ≫ T.map
            (schemeDerivedBaseChangeMap fA (pullback.snd fA gA) gA (pullback.fst fA gA)
              pullback.condition E ≫ (schemeDerivedDirectImage (pullback.snd fA gA)).map c0)
      := by
  obtain ⟨c0, hc0⟩ := exists_isDerivedModulePullbackComparison
    (pullback.fst (f ≫ eS.hom) (eT.inv ≫ g ≫ eS.hom)) G
  obtain ⟨a, b, hab⟩ := canonicalModuleBaseChange_iso_comparison_ab f g g' f' sq G c hc eS eT c0 hc0
  exact ⟨c0, hc0, a, b, hab⟩

end AlgebraicGeometry
