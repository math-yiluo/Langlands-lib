/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.AlgebraicGeometry.RelativeMVRestrictionSourceCounit
import WeilConjectures.AlgebraicGeometry.RelativeMVRestrictionTargetCounit

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The fixed adjunction data require a larger elaboration budget.
private theorem restriction_coefficients
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {B A X S : Scheme.{u}} (k : B ⟶ A) (j : A ⟶ X) (l : B ⟶ X)
    (h : k ≫ j = l) (f : X ⟶ S) {K L : schemeDerivedCategory X} (ψ : K ⟶ L) :
    (schemeDerivedDirectImage (j ≫ f)).map ((derivedPullback j).map ψ) ≫
        relativeMVRestriction k j l h f L =
      relativeMVRestriction k j l h f K ≫
        (schemeDerivedDirectImage (l ≫ f)).map ((derivedPullback l).map ψ) := by
  let c := relativeMVComp k j ≪≫
    eqToIso (congrArg (fun t : B ⟶ X ↦ derivedPullback t) h)
  have hb :
      (schemeDerivedDirectImage j).map ((derivedPullback j).map ψ) ≫
          (relativeMVAdj l).homEquiv _ _
            (c.inv.app ((schemeDerivedDirectImage j).obj ((derivedPullback j).obj L)) ≫
              (derivedPullback k).map
                ((relativeMVAdj j).counit.app ((derivedPullback j).obj L)) ≫ c.hom.app L) =
        (relativeMVAdj l).homEquiv _ _
            (c.inv.app ((schemeDerivedDirectImage j).obj ((derivedPullback j).obj K)) ≫
              (derivedPullback k).map
                ((relativeMVAdj j).counit.app ((derivedPullback j).obj K)) ≫ c.hom.app K) ≫
          (schemeDerivedDirectImage l).map ((derivedPullback l).map ψ) := by
    rw [← (relativeMVAdj l).homEquiv_naturality_left,
      ← (relativeMVAdj l).homEquiv_naturality_right]
    apply congrArg ((relativeMVAdj l).homEquiv _ _)
    rw [c.inv.naturality_assoc]
    simp only [Functor.comp_map]
    rw [← Functor.map_comp_assoc]
    have hn := (relativeMVAdj j).counit.naturality ((derivedPullback j).map ψ)
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [hn]
    simp only [Functor.map_comp, Category.assoc]
    have hn := c.hom.naturality ψ
    dsimp only [Functor.comp_map] at hn
    simpa only [Category.assoc] using congrArg
      (fun t ↦ c.inv.app _ ≫ (derivedPullback k).map
        ((relativeMVAdj j).counit.app ((derivedPullback j).obj K)) ≫ t) hn
  unfold relativeMVRestriction
  dsimp only
  simp only [Category.assoc]
  rw [(relativeMVImageComp j f).inv.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, hb, Functor.map_comp]
  simp only [Category.assoc]
  have hn := (relativeMVImageComp l f).hom.naturality ((derivedPullback l).map ψ)
  dsimp only [Functor.comp_map] at hn
  rw [hn]

private theorem localArrow_factor
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (W : X.Opens) :
    (relativeMVLocalArrow f f' g g' hpull K K' φ W).hom =
      (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K) (𝟙 _) W).hom ≫
        (schemeDerivedDirectImage (pullback.fst g' W.ι ≫ f')).map
          ((derivedPullback (pullback.fst g' W.ι)).map φ) := by
  simp only [relativeMVLocalArrow, Arrow.mk_hom, Functor.map_comp, Category.assoc]
  rw [(derivedPullback (pullback.fst g' W.ι)).map_id]
  erw [(schemeDerivedDirectImage (pullback.fst g' W.ι ≫ f')).map_id]
  simp only [Category.id_comp]

/-- Base change commutes with relative restriction along one inclusion of opens.
Source: Stacks Project, Cohomology, Tags 08HY, 08BV and 08HZ.
(blueprint: new-relative-mv-second).
Proof: Expand relativeMVRestriction as the mate of the restricted counit and
cancel the right-adjoint composition comparisons on both paths. Transpose under
the adjunction for W and its inverse-image open. The resulting maps are
composites of pullbacks of the same counit. Naturality of that counit and of φ
identifies their middle factors; associativity of the pinned pullback
composition comparisons identifies the outside factors. The lift identities
for relativeMVOpenLift give equality of the two projections, hence the equality
transport appearing in the local comparison is precisely the one in the
restriction. Injectivity of the adjunction Hom equivalence gives the claimed
square. No strictness of the inclusion is used, so equality and empty opens
are included. -/
theorem relativeMV_restriction_naturality
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (W U : X.Opens) (i : W ≤ U) :
    (derivedPullback g).map
        (relativeMVRestriction (X.homOfLE i) U.ι W.ι (Scheme.homOfLE_ι X i) f K) ≫
      (relativeMVLocalArrow f f' g g' hpull K K' φ W).hom =
      (relativeMVLocalArrow f f' g g' hpull K K' φ U).hom ≫
        relativeMVRestriction (relativeMVOpenLift g' i) (pullback.fst g' U.ι)
          (pullback.fst g' W.ι) (pullback.lift_fst _ _ _) f' K' := by
  rw [localArrow_factor f f' g g' hpull K K' φ W,
    localArrow_factor f f' g g' hpull K K' φ U]
  have hc :
      (derivedPullback g).map
          (relativeMVRestriction (X.homOfLE i) U.ι W.ι (Scheme.homOfLE_ι X i) f K) ≫
        (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K) (𝟙 _) W).hom =
      (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K) (𝟙 _) U).hom ≫
        relativeMVRestriction (relativeMVOpenLift g' i) (pullback.fst g' U.ι)
          (pullback.fst g' W.ι) (pullback.lift_fst _ _ _) f' ((derivedPullback g').obj K) := by
    apply ((relativeMVAdj (pullback.fst g' W.ι ≫ f')).homEquiv _ _).symm.injective
    exact (relativeMV_restriction_source_counit f f' g g' hpull K W U i).trans
      (relativeMV_restriction_target_counit f f' g g' hpull K W U i).symm
  have hn := restriction_coefficients (relativeMVOpenLift g' i) (pullback.fst g' U.ι)
    (pullback.fst g' W.ι) (pullback.lift_fst _ _ _) f' φ
  simp only [← Category.assoc]
  rw [hc]
  simp only [Category.assoc]
  rw [← hn]

end AlgebraicGeometry
