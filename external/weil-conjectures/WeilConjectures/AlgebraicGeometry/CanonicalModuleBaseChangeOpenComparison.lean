/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps

import WeilConjectures.AlgebraicGeometry.DerivedModulePullbackComparison
import WeilConjectures.AlgebraicGeometry.CanonicalModuleBaseChangeOpenComparisonCompat

/-! # Canonical module base change under open restriction

Source: Stacks Project, Tags 08FE and 08HY; the local reduction in Tag 08IB.
(blueprint: lem-pc-canonical-module-base-change-open-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- Restriction identifies the module base-change arrow with the arrow of the
chosen pullback of the restricted maps. No affine chart is used.
Source: Stacks Project, Tag 08FE, proof; Tag 08HY, counit construction;
Tag 08IB, first proof paragraph; Tag 0D5U, exact extension by zero.
(blueprint: lem-pc-canonical-module-base-change-open-comparison).

Proof:
1. Put U = f inverse image of V and Z = f' inverse image of W. The restricted
square with vertices Z,U,W,V is cartesian: a map to U and W agreeing over V
composes to a cone for the original square, whose unique lift lands in Z.
Identify Z with the chosen pullback of f restricted to V and g restricted from
W to V. Both projections agree under this identification.
2. Apply the pullback restriction comparison to g and direct-image restriction
to f. Exact restriction takes G[0] to H[0], yielding a. Apply direct-image
restriction to f', and identify restriction of g'^*G with the ordinary pullback
of H under the first projection, yielding b. These are isomorphisms.
3. Unpack hc as a left-derived counit epsilon. For a complex K on U, evaluate
epsilon on its termwise extension by zero to X, restrict the result to Z, and
use the projection comparisons to regard it as a counit for the first projection.
Extension by zero is exact and preserves K-flatness: tensoring an extension by
zero with a test complex is extension by zero of the tensor with its restriction,
and both restriction and extension by zero preserve acyclicity. Thus the new
counit is invertible on K-flat representatives and has the left-derived universal
property. Naturality at the extension-by-zero counit j_!(M|U) -> M shows that its
value on M|U agrees with epsilon on M restricted to Z. In particular this holds
for M = G[0]. Compose the value on H[0] with the single-complex identification
to obtain c0 and its comparison predicate (exists_isDerivedModulePullbackComparison).
4. Transpose the derived mate of Tag 08HY under the restricted adjunction.
The open-square identity for underived mates commutes with restriction on
complexes. Localizing and using the derived adjunction equations gives the same
identity for the derived mate. Naturality of the direct-image restriction
comparison then composes this identity with the transported epsilon, giving the
displayed square. No invertibility of the base-change arrow is asserted.
The argument is valid for empty opens and the zero module. -/
theorem exists_canonicalModuleBaseChange_open_comparison
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
    (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    let U := f ⁻¹ᵁ V
    let fA := f ∣_ V
    let gA := g.resLE V W hWV
    let H := (schemeOpenRestriction X U).obj G
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
    let E0 := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj H
    let R := (schemeOpenRestriction S' W).mapDerivedCategory
    ∃ c0 : (derivedPullback (pullback.fst fA gA)).obj E0 ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H),
      IsDerivedModulePullbackComparison (pullback.fst fA gA) H c0 ∧
      ∃ a : R.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) ≅
          (derivedPullback gA).obj ((schemeDerivedDirectImage fA).obj E0),
      ∃ b : R.obj ((schemeDerivedDirectImage f').obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
                ((Scheme.Modules.tensorPullback g').obj G))) ≅
          (schemeDerivedDirectImage (pullback.snd fA gA)).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
                ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H)),
        R.map (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
            (schemeDerivedDirectImage f').map c) ≫ b.hom =
          a.hom ≫
            (schemeDerivedBaseChangeMap fA (pullback.snd fA gA) gA (pullback.fst fA gA)
              pullback.condition E0 ≫ (schemeDerivedDirectImage (pullback.snd fA gA)).map c0)
      := by
  intro U fA gA H E E0 R
  obtain ⟨c0, hc0⟩ := exists_isDerivedModulePullbackComparison.{u, w}
    (pullback.fst fA gA) H
  exact ⟨c0, hc0,
    restricted_base_change_compatibility.{u, w} f g g' f' sq G c hc V W hWV c0 hc0⟩

end AlgebraicGeometry
