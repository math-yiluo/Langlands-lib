/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVExactOpenComparison
import WeilConjectures.AlgebraicGeometry.RelativeMVInverseOpenMate

/-! # Inverse-image open comparisons with units, restrictions, and base change

Source: Stacks Project, Cohomology, Tags 08BV, 08HZ and 08HY.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- Comparisons on individual inverse-image opens, compatible with their units,
restrictions along one inclusion, and the pasted base-change map.

Source: Stacks Project, Cohomology, Tags 08BV, 08HZ and 08HY; Derived Categories
of Schemes, Tag 0DJ9, the open vertices of the induction diagram.
(blueprint: lem-pc-relative-mv-inverse-open-comparisons).

Proof: For each W use pullbackRestrictIsoRestrict g' W to identify the chosen
pullback with the inverse-image open, preserving both projections. Derive this
scheme isomorphism, and use left-adjoint uniqueness to identify exact restriction
with pullback on the inverse-image open. Compose the resulting direct-image
comparison with relativeMVImageComp for the projection to X' followed by f'.
This constructs the entire family e, independently of the source object map.
The left-adjoint uniqueness unit identity and the right-adjoint composition unit
identity prove the first formula. For an inclusion W≤U, the projection-preserving
scheme comparisons carry the inverse-image inclusion to relativeMVOpenLift:
check its two projections and use pullback hom-ext. Transpose both restriction
maps under the W adjunction. The counit identity for adjoint uniqueness and the
canonical derived composition coherence identify the two transposes, proving
the second formula. For the third formula expand mvBaseChangeOpenMap and each
base-change map as the mate of the pulled-back counit. Substitute the counit of
a composite adjunction. Naturality moves the object map to the last factor;
the two triangle identities cancel the intermediate unit-counit pairs. Pinned
pullback associativity identifies the remaining two comparisons, and the equality
of the two pullback projection composites gives exactly the equality transport
in relativeMVLocalArrow. Thus the remaining composite is its hom preceded by
the mapped relativeMVExactOpenIso. These identities hold for arbitrary opens,
including the empty open, and arbitrary object maps, including zero maps. No
cover or distinguishedness assertion is involved. -/
theorem relativeMV_inverse_open_comparisons
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') :
    ∃ e : ∀ W : X.Opens,
      (schemeDerivedDirectImage f').obj
        ((schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).obj
          ((schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.obj K')) ≅
        (relativeMVLocalArrow f f' g g' hpull K K' φ W).right,
      (∀ W : X.Opens,
        (schemeDerivedDirectImage f').map
            ((mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ W)).unit.app K') ≫ (e W).hom =
          relativeMVUnit (pullback.fst g' W.ι) f' K') ∧
      (∀ (W U : X.Opens) (i : W ≤ U),
        (schemeDerivedDirectImage f').map
            (schemeDerivedOpenDirectImageRestriction X'
              ((TopologicalSpace.Opens.map g'.base).map (homOfLE i))
              (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U))
              (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ W)) K') ≫ (e W).hom =
          (e U).hom ≫ relativeMVRestriction (relativeMVOpenLift g' i)
            (pullback.fst g' U.ι) (pullback.fst g' W.ι)
            (pullback.lift_fst _ _ _) f' K') ∧
      (∀ W : X.Opens,
        mvBaseChangeOpenMap f f' g g' hpull.w K K' φ W ≫ (e W).hom =
          ((derivedPullback g).mapIso (relativeMVExactOpenIso f W K)).hom ≫
            (relativeMVLocalArrow f f' g g' hpull K K' φ W).hom) := by
  refine ⟨fun W ↦ relativeMVInverseOpenIso g' f' W K', ?_, ?_, ?_⟩
  · intro W
    exact relativeMVInverseOpenIso_unit g' f' W K'
  · intro W U i
    exact relativeMVInverseOpenIso_restriction g' f' i K'
  · intro W
    exact relativeMVInverseOpenIso_mate f f' g g' hpull K K' φ W

end AlgebraicGeometry
