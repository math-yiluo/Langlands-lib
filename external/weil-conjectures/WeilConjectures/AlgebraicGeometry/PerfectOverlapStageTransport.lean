/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapStageEquivalenceFunctor

/-! # Derived transport with the cartesian stage interfaces -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local irreducible] perfectHomComposition
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The fixed derived transport, with its endpoints expressed by the stage functors.
Source: Stacks Project, Tags 08DW and 0D5S. The forward stage functor is derived
pullback along the inverse cartesian isomorphism. Rewrite these two functors
by their proved equations and use the explicitly constructed derived transport.
(blueprint: def-pc-perfect-overlap-stage-transport). -/
@[irreducible] noncomputable def perfectOverlapStageTransport
    {X Y K C T S : Scheme.{u}}
    (g : X ⟶ Y) (f : K ⟶ Y)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S)
    (hg : IsPullback g pX pY b) (hf : IsPullback f pK pY q)
    (U V : Y.Opens)
    (r : (g ⁻¹ᵁ (U ⊓ V)).toScheme ⟶ (f ⁻¹ᵁ (U ⊓ V)).toScheme)
    (m : pullback ((U ⊓ V).ι ≫ pY) b ⟶ pullback ((U ⊓ V).ι ≫ pY) q)
    (hmap :
      ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback.inv ≫ r =
        m ≫ ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback.inv) :
    derivedPullback r ⋙ (perfectOverlapStageEquivalence g pX pY b hg U V).functor ≅
      (perfectOverlapStageEquivalence f pK pY q hf U V).functor ⋙
        derivedPullback m := by
  rw [perfectOverlapStageEquivalence_functor_eq, perfectOverlapStageEquivalence_functor_eq]
  exact perfectOverlapDerivedPullbackTransport r
    ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback
    ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback m hmap

end AlgebraicGeometry
