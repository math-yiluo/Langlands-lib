/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps

/-! # The counit for base change of a composite morphism

Source: Stacks Project, Cohomology, Tags 08HY, 08HZ and 0D5S.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

/-- The right-adjoint composition mate preserves the composite counit. -/
private theorem imageComp_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {B X S : Scheme.{u}} (l : B ⟶ X) (f : X ⟶ S)
    (E : schemeDerivedCategory B) :
    (derivedPullback (l ≫ f)).map ((relativeMVImageComp l f).hom.app E) ≫
        (relativeMVAdj (l ≫ f)).counit.app E =
      (relativeMVComp l f).inv.app
          ((schemeDerivedDirectImage f).obj ((schemeDerivedDirectImage l).obj E)) ≫
        (derivedPullback l).map
          ((relativeMVAdj f).counit.app ((schemeDerivedDirectImage l).obj E)) ≫
        (relativeMVAdj l).counit.app E := by
  simpa only [relativeMVImageComp, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_counit_app,
    Functor.comp_obj,
    Category.assoc] using
    ((((relativeMVAdj f).comp (relativeMVAdj l)).ofNatIsoLeft
      (relativeMVComp l f)).rightAdjointUniq_hom_app_counit
        (relativeMVAdj (l ≫ f)) E)

/-- Transposing relative restriction cancels its inner adjunction transpose. -/
private theorem restriction_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {B A X S : Scheme.{u}} (k : B ⟶ A) (j : A ⟶ X) (l : B ⟶ X)
    (h : k ≫ j = l) (f : X ⟶ S) (K : schemeDerivedCategory X) :
    let A := (schemeDerivedDirectImage (j ≫ f)).obj ((derivedPullback j).obj K)
    let C := (schemeDerivedDirectImage j).obj ((derivedPullback j).obj K)
    let c := relativeMVComp k j ≪≫
      eqToIso (congrArg (fun t : B ⟶ X ↦ derivedPullback t) h)
    (derivedPullback (l ≫ f)).map (relativeMVRestriction k j l h f K) ≫
        (relativeMVAdj (l ≫ f)).counit.app ((derivedPullback l).obj K) =
      (relativeMVComp l f).inv.app A ≫
        (derivedPullback l).map
          ((derivedPullback f).map
              ((relativeMVImageComp j f).inv.app ((derivedPullback j).obj K)) ≫
            (relativeMVAdj f).counit.app C) ≫
        c.inv.app C ≫
        (derivedPullback k).map
          ((relativeMVAdj j).counit.app ((derivedPullback j).obj K)) ≫ c.hom.app K := by
  dsimp only
  unfold relativeMVRestriction
  dsimp only
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [imageComp_counit]
  rw [(relativeMVComp l f).inv.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc]
  erw [(relativeMVAdj f).counit.naturality]
  simp only [Functor.id_map, Functor.map_comp, Category.assoc]
  erw [← (relativeMVAdj l).homEquiv_counit]
  simp only [Functor.id_obj, Equiv.symm_apply_apply]
  rw [(relativeMVComp l f).inv.naturality_assoc]
  simp only [Functor.comp_map]

/-- Naturality of restriction transposition for an arbitrary incoming arrow. -/
private theorem restriction_transpose
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {B A X S : Scheme.{u}} (k : B ⟶ A) (j : A ⟶ X) (l : B ⟶ X)
    (h : k ≫ j = l) (f : X ⟶ S) (K : schemeDerivedCategory X)
    (T : schemeDerivedCategory S)
    (a : T ⟶ (schemeDerivedDirectImage (j ≫ f)).obj ((derivedPullback j).obj K)) :
    let C := (schemeDerivedDirectImage j).obj ((derivedPullback j).obj K)
    let c := relativeMVComp k j ≪≫
      eqToIso (congrArg (fun t : B ⟶ X ↦ derivedPullback t) h)
    ((relativeMVAdj (l ≫ f)).homEquiv _ _).symm
        (a ≫ relativeMVRestriction k j l h f K) =
      (relativeMVComp l f).inv.app T ≫
        (derivedPullback l).map
          (((relativeMVAdj f).homEquiv _ _).symm
            (a ≫ (relativeMVImageComp j f).inv.app ((derivedPullback j).obj K))) ≫
        c.inv.app C ≫
        (derivedPullback k).map
          ((relativeMVAdj j).counit.app ((derivedPullback j).obj K)) ≫ c.hom.app K := by
  dsimp only
  change (derivedPullback (l ≫ f)).map (a ≫ relativeMVRestriction k j l h f K) ≫
    (relativeMVAdj (l ≫ f)).counit.app ((derivedPullback l).obj K) = _
  rw [Functor.map_comp, Category.assoc, restriction_counit]
  rw [← Category.assoc, (relativeMVComp l f).inv.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  rfl

/-- The inverse-image inclusion preserves the first pullback projection.
Source: Stacks Project, Cohomology, Tag 08HY; the universal property of pullbacks.
Proof: The inclusion is the pullback lift with first component the projection
from the smaller inverse-image open. The first projection equation for this
lift gives the assertion. No hypothesis beyond the inclusion is needed, so
this holds for equal opens and for an empty open as well. -/
private theorem relativeMVOpenLift_fst {X X' : Scheme.{u}} (g' : X' ⟶ X)
    {W U : X.Opens} (i : W ≤ U) :
    relativeMVOpenLift g' i ≫ pullback.fst g' U.ι = pullback.fst g' W.ι :=
  pullback.lift_fst _ _ _

/-- The comparison is independent of which proof witnesses the projection equation.
The named witness pins its source before applying congrArg; congruence and proof
irrelevance identify the resulting isomorphisms. -/
private theorem comparison_witness_eq
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) {W U : X.Opens} (i : W ≤ U) :
    (relativeMVComp (relativeMVOpenLift g' i) (pullback.fst g' U.ι) ≪≫
      eqToIso (congrArg (fun t : pullback g' W.ι ⟶ X' ↦ derivedPullback t)
        (pullback.lift_fst _ _ _))) =
    (relativeMVComp (relativeMVOpenLift g' i) (pullback.fst g' U.ι) ≪≫
      eqToIso (congrArg (fun t : pullback g' W.ι ⟶ X' ↦ derivedPullback t)
        (relativeMVOpenLift_fst g' i))) := by
  congr 1

/-- Transposing the target restriction removes the direct-image composition mates.
Source: Stacks Project, Cohomology, Tags 08HY, 08HZ and 0D5S.
(blueprint: new-relative-mv-composite-base-change-target-transpose).
Proof: Expand relativeMVRestriction. Its three factors are the inverse U',f'
right-adjoint comparison, Rf' applied to the adjoint of the restricted open counit,
and the W',f' right-adjoint comparison. Naturality in the source of the adjunction
Hom equivalence moves the incoming local arrow and inverse U',f' comparison
through the transpose. The mate identity for the final W',f' comparison replaces
its composite counit by the inverse pullback composition comparison followed by
L(W'→X') of the f' counit and then the W' counit. Naturality moves the middle
Rf' map through the f' counit. The triangle identity cancels the transpose of
the restricted open counit. Naturality of the inverse pullback comparison then
moves the incoming arrow to the f' transpose. The remaining three factors are
exactly the inverse c', pulled-back U' counit, and c' at Lg'K shown below.
The base-change map in the local arrow is neither expanded nor computed.
This argument uses only adjunction naturality and the mate counit identity, so
equal opens, empty opens and zero objects satisfy it without extra hypotheses. -/
theorem relativeMV_composite_baseChange_target_transpose
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (W U : X.Opens) (i : W ≤ U) :
    let c' := relativeMVComp (relativeMVOpenLift g' i) (pullback.fst g' U.ι) ≪≫
      eqToIso (congrArg (fun t : pullback g' W.ι ⟶ X' ↦ derivedPullback t)
        (pullback.lift_fst _ _ _))
    ((relativeMVAdj (pullback.fst g' W.ι ≫ f')).homEquiv _ _).symm
      ((relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K)
          (𝟙 _) U).hom ≫
        relativeMVRestriction (relativeMVOpenLift g' i) (pullback.fst g' U.ι)
          (pullback.fst g' W.ι) (pullback.lift_fst _ _ _) f'
          ((derivedPullback g').obj K)) =
    (relativeMVComp (pullback.fst g' W.ι) f').inv.app
      (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K) (𝟙 _) U).left ≫
      (derivedPullback (pullback.fst g' W.ι)).map
        (((relativeMVAdj f').homEquiv _ _).symm
          ((relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K)
              (𝟙 _) U).hom ≫
            (relativeMVImageComp (pullback.fst g' U.ι) f').inv.app
              ((derivedPullback (pullback.fst g' U.ι)).obj
                ((derivedPullback g').obj K)))) ≫
      c'.inv.app ((schemeDerivedDirectImage (pullback.fst g' U.ι)).obj
        ((derivedPullback (pullback.fst g' U.ι)).obj ((derivedPullback g').obj K))) ≫
      (derivedPullback (relativeMVOpenLift g' i)).map
        ((relativeMVAdj (pullback.fst g' U.ι)).counit.app
          ((derivedPullback (pullback.fst g' U.ι)).obj ((derivedPullback g').obj K))) ≫
      c'.hom.app ((derivedPullback g').obj K) := by
  dsimp only
  rw [comparison_witness_eq]
  exact restriction_transpose (relativeMVOpenLift g' i) (pullback.fst g' U.ι)
    (pullback.fst g' W.ι) (relativeMVOpenLift_fst g' i) f' ((derivedPullback g').obj K)
    (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K) (𝟙 _) U).left
    (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K) (𝟙 _) U).hom

end AlgebraicGeometry
