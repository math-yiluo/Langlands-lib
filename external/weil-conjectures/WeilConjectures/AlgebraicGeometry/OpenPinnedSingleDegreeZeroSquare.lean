/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.PinnedSingleBaseChangeShift
import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroTarget

/-! # Degree-zero geometric open restriction square for pinned tensor counits
Source: Stacks Project, Tags 08FE, 08HY, 08IB and 0D5U.
(blueprint: lem-pc-open-pinned-single-degree-zero-square). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

/-- Open restriction square in degree zero for the composition-pinned counits.
Source: Stacks Project, Tags 08FE, 08HY, 08IB and 0D5U.
(blueprint: lem-pc-open-pinned-single-degree-zero-square).
Proof: identify the inverse image of W in X' with the pullback of the restricted
square by the universal property. Restriction preserves K-injectives because
extension by zero is an exact left adjoint. It preserves K-flat complexes by
extending acyclic test complexes by zero and using the tensor projection formula.
Compute Rf and Lg on these resolutions and use exact restriction of single
complexes to construct a. Combine the Rf' comparison with tensor restriction
and the same single-complex identification to construct b. Transpose both
base-change composites under the pinned derived adjunctions. Their transposes
are tensor reassociation followed by pullback of the direct-image counit.
The underived restriction mate identity holds termwise, including its units,
counits and reassociations. Localize it on the chosen resolutions. Equality of
transposes gives equality of the mates. The last single-component maps are
precisely the composition-pinned tensor counits. Naturality in G gives one pair
a,b for all modules. Empty opens and zero modules require no exceptions. -/
theorem open_pinned_single_degree_zero_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    let U := f ⁻¹ᵁ V
    let fA := f ∣_ V
    let gA := g.resLE V W hWV
    let p := pullback.fst fA gA
    let q := pullback.snd fA gA
    let R := (schemeOpenRestriction S' W).mapDerivedCategory
    ∃ a : singleDegreeBaseChangeSource.{u, w} f g 0 ⋙ R ≅
        schemeOpenRestriction X U ⋙ singleDegreeBaseChangeSource.{u, w} fA gA 0,
    ∃ b : singleDegreeBaseChangeTarget.{u, w} g' f' 0 ⋙ R ≅
        schemeOpenRestriction X U ⋙ singleDegreeBaseChangeTarget.{u, w} p q 0,
    ∀ G : X.Modules,
      R.map (singleDegreeBaseChangeComposite f g g' f' sq.w 0 G) ≫ b.hom.app G =
        a.hom.app G ≫
          singleDegreeBaseChangeComposite fA gA p q pullback.condition 0
            ((schemeOpenRestriction X U).obj G) := by
  dsimp
  obtain ⟨b, hb⟩ := open_pinned_single_degree_zero_target f g g' f' sq V W hWV
  exact ⟨openPinnedSingleDegreeZeroSourceIso f g V W hWV, b, hb⟩

end AlgebraicGeometry
