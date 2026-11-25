/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps

/-! # A counit normal form for the relative restriction square

Source: Stacks Project, Cohomology, Tags 08HY, 08BV and 08HZ.
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

/-- Base-change transposition is natural in the input and coefficient morphisms. -/
private theorem baseChange_transpose
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (q : X' ⟶ X)
    (h : q ≫ f = f' ≫ g) (E : schemeDerivedCategory X)
    (A : schemeDerivedCategory S) (a : A ⟶ (schemeDerivedDirectImage f).obj E)
    (Y : schemeDerivedCategory X') (b : (derivedPullback q).obj E ⟶ Y) :
    ((relativeMVAdj f').homEquiv _ _).symm
        ((derivedPullback g).map a ≫ schemeDerivedBaseChangeMap f f' g q h E ≫
          (schemeDerivedDirectImage f').map b) =
      (relativeMVComp f' g).hom.app A ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj A) h.symm) ≫
        (relativeMVComp q f).inv.app A ≫
        (derivedPullback q).map
          ((derivedPullback f).map a ≫ (relativeMVAdj f).counit.app E) ≫ b := by
  let s := relativeMVComp f' g ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm) ≪≫ (relativeMVComp q f).symm
  change ((relativeMVAdj f').homEquiv _ _).symm
      ((derivedPullback g).map a ≫
        (relativeMVAdj f').homEquiv _ _
          ((relativeMVComp f' g).hom.app _ ≫
            eqToHom (congrArg (fun k ↦ (derivedPullback k).obj _) h.symm) ≫
            (relativeMVComp q f).inv.app _ ≫
            (derivedPullback q).map ((relativeMVAdj f).counit.app E)) ≫
        (schemeDerivedDirectImage f').map b) = _
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm, Equiv.symm_apply_apply]
  have hn := s.hom.naturality a
  simp only [Functor.comp_map] at hn
  have hn' : (derivedPullback f').map ((derivedPullback g).map a) ≫
      s.hom.app ((schemeDerivedDirectImage f).obj E) =
      s.hom.app A ≫ (derivedPullback q).map ((derivedPullback f).map a) := hn
  have hs (T : schemeDerivedCategory S) : s.hom.app T =
      (relativeMVComp f' g).hom.app T ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj T) h.symm) ≫
        (relativeMVComp q f).inv.app T := by
    simp only [s, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
      eqToHom_app, Iso.symm_hom]
  simp only [← hs, ← Category.assoc]
  rw [hn']
  simp only [Functor.map_comp, Category.assoc]

/-- The source path has the explicit restricted-counit normal form.
Source: Stacks Project, Cohomology, Tags 08HY, 08BV and 08HZ.
(blueprint: new-relative-mv-restriction-source-counit).
Proof: Transpose only the source path under L(W'→S') adjoint to R(W'→S').
Functoriality of the Hom equivalence moves Lg(restriction) to the left of the
base-change transpose and the coefficient comparison to its right. By 08HY,
the base-change transpose is the pullback square comparison followed by
L(W'→W) of the counit for W→S. Naturality of the square comparison moves
restriction inside this pullback. Expand relativeMVRestriction. The mate
identity for relativeMVImageComp W.ι f replaces its last factor by the counit
of the composite adjunction, precomposed with (relativeMVComp W.ι f).inv.
Naturality moves the initial direct-image comparison through that inverse
pullback comparison. The composite counit is L(W→X) of the counit for f,
followed by the counit for W→X. The triangle identity cancels the Hom-equivalence
transpose defining the middle factor of restriction. What remains is precisely
the displayed pullback of the two restricted counits, followed by the W
coefficient comparison. No triple-composition coherence and no target path
are used in this calculation. Equal and empty opens satisfy the same identities. -/
theorem relativeMV_restriction_source_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (W U : X.Opens) (i : W ≤ U) :
    let A := (schemeDerivedDirectImage (U.ι ≫ f)).obj ((derivedPullback U.ι).obj K)
    let c := relativeMVComp (X.homOfLE i) U.ι ≪≫
      eqToIso (congrArg (fun t : W.toScheme ⟶ X ↦ derivedPullback t)
        (Scheme.homOfLE_ι X i))
    let t := (relativeMVComp (pullback.fst g' W.ι ≫ f') g).hom.app A ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj A)
        (show pullback.snd g' W.ι ≫ (W.ι ≫ f) =
            (pullback.fst g' W.ι ≫ f') ≫ g by
          rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc]).symm) ≫
      (relativeMVComp (pullback.snd g' W.ι) (W.ι ≫ f)).inv.app A ≫
      (derivedPullback (pullback.snd g' W.ι)).map
        ((relativeMVComp W.ι f).inv.app A ≫
          (derivedPullback W.ι).map
            ((derivedPullback f).map
                ((relativeMVImageComp U.ι f).inv.app ((derivedPullback U.ι).obj K)) ≫
              (relativeMVAdj f).counit.app
                ((schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K))) ≫
          c.inv.app ((schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K)) ≫
          (derivedPullback (X.homOfLE i)).map
            ((relativeMVAdj U.ι).counit.app ((derivedPullback U.ι).obj K)) ≫
          c.hom.app K) ≫
      (relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := W.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' W.ι) g').inv.app K
    ((relativeMVAdj (pullback.fst g' W.ι ≫ f')).homEquiv _ _).symm
      ((derivedPullback g).map
          (relativeMVRestriction (X.homOfLE i) U.ι W.ι (Scheme.homOfLE_ι X i) f K) ≫
        (relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K)
          (𝟙 _) W).hom) = t := by
  dsimp only
  unfold relativeMVLocalArrow
  simp only [Arrow.mk_hom]
  rw [baseChange_transpose]
  rw [restriction_counit]
  rw [(derivedPullback (pullback.fst g' W.ι)).map_id]
  erw [Category.comp_id]

end AlgebraicGeometry
