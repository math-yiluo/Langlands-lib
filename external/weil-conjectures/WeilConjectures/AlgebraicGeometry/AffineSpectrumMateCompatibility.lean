/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCounitCompatibility
import WeilConjectures.AlgebraicGeometry.AffineSpectrumComparisonCancellation
import WeilConjectures.AlgebraicGeometry.AffineSpectrumPullbackSquareCoherence
import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation

/-! # Compatibility of the canonical spectrum comparisons with base-change mates

Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-pc-affine-spectrum-mate-compatibility).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

private theorem counit_postcompose {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {M : C} {N N' : D}
    (t : M ⟶ G.obj N) (d : N ⟶ N') :
    F.map (t ≫ G.map d) ≫ adj.counit.app N' =
      (F.map t ≫ adj.counit.app N) ≫ d := by
  simpa only [Adjunction.homEquiv_counit] using
    adj.homEquiv_naturality_right_symm t d

private theorem counit_ext {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {M : C} {N : D}
    {t t' : M ⟶ G.obj N}
    (h : F.map t ≫ adj.counit.app N = F.map t' ≫ adj.counit.app N) : t = t' :=
  (adj.homEquiv M N).symm.injective h

private theorem mate_coordinate_ext {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {M : C} {E : D}
    {R : D ⥤ C} (b : G ≅ R) (ev : F.obj (R.obj E) ⟶ E)
    (beta : M ⟶ G.obj E) (rhs : M ⟶ R.obj E)
    (hc : F.map (b.hom.app E) ≫ ev = adj.counit.app E)
    (heval : F.map rhs ≫ ev = F.map beta ≫ adj.counit.app E) :
    beta ≫ b.hom.app E = rhs := by
  have hi : F.map (b.inv.app E) ≫ adj.counit.app E = ev := by
    rw [← hc]
    simp only [← Category.assoc, ← Functor.map_comp, b.inv_hom_id_app]
    rw [F.map_id, Category.id_comp]
  apply (cancel_mono (b.inv.app E)).mp
  apply counit_ext adj
  simp only [Category.assoc, b.hom_inv_id_app, Functor.map_comp]
  rw [F.map_id, Category.id_comp, hi, heval]

private theorem coordinate_mate_compatibility
    {A B A' B' A0 B0 A0' B0' : Type*}
    [Category A] [Category B] [Category A'] [Category B']
    [Category A0] [Category B0] [Category A0'] [Category B0']
    (F : B ⥤ A) (R : A ⥤ B) (F' : B' ⥤ A') (R' : A' ⥤ B')
    (G : B ⥤ B') (G' : A ⥤ A')
    (F0 : B0 ⥤ A0) (R0 : A0 ⥤ B0) (F0' : B0' ⥤ A0') (R0' : A0' ⥤ B0')
    (G0 : B0 ⥤ B0') (G0' : A0 ⥤ A0')
    (U : A ⥤ A0) (U' : A' ⥤ A0') (V : A0 ⥤ A) (V' : A0' ⥤ A')
    (T : B0 ⥤ B) (T' : B0' ⥤ B')
    (adj : F ⊣ R) (adj' : F' ⊣ R') (adj0 : F0 ⊣ R0) (adj0' : F0' ⊣ R0')
    (b : R ≅ U ⋙ R0 ⋙ T) (b' : R' ≅ U' ⋙ R0' ⋙ T')
    (aF : T ⋙ F ≅ F0 ⋙ V) (aF' : T' ⋙ F' ≅ F0' ⋙ V')
    (aG : T ⋙ G ≅ G0 ⋙ T') (aG' : V ⋙ G' ≅ G0' ⋙ V')
    (dG : U ⋙ G0' ≅ G' ⋙ U')
    (src : R ⋙ G ≅ U ⋙ R0 ⋙ G0 ⋙ T')
    (hsrc : src = Functor.isoWhiskerRight b G ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft U (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft R0 aG))
    (e : ∀ K : A, V.obj (U.obj K) ⟶ K)
    (e' : ∀ K : A', V'.obj (U'.obj K) ⟶ K)
    (q : ∀ M : B, F'.obj (G.obj M) ⟶ G'.obj (F.obj M))
    (q0 : ∀ N : B0, F0'.obj (G0.obj N) ⟶ G0'.obj (F0.obj N))
    (hc : ∀ K : A, F.map (b.hom.app K) ≫ aF.hom.app (R0.obj (U.obj K)) ≫
      V.map (adj0.counit.app (U.obj K)) ≫ e K = adj.counit.app K)
    (hc' : ∀ K : A', F'.map (b'.hom.app K) ≫ aF'.hom.app (R0'.obj (U'.obj K)) ≫
      V'.map (adj0'.counit.app (U'.obj K)) ≫ e' K = adj'.counit.app K)
    (hcancel : ∀ K : A, aG'.hom.app (U.obj K) ≫ V'.map (dG.hom.app K) ≫
      e' (G'.obj K) = G'.map (e K))
    (hsquare : ∀ (M : B) (N : B0) (k : M ⟶ T.obj N),
      F'.map (G.map k ≫ aG.hom.app N) ≫ aF'.hom.app (G0.obj N) ≫ V'.map (q0 N) =
      q M ≫ G'.map (F.map k) ≫ G'.map (aF.hom.app N) ≫ aG'.hom.app (F0.obj N))
    (K : A) (beta : G.obj (R.obj K) ⟶ R'.obj (G'.obj K))
    (beta0 : G0.obj (R0.obj (U.obj K)) ⟶ R0'.obj (G0'.obj (U.obj K)))
    (hbeta : F'.map beta ≫ adj'.counit.app (G'.obj K) =
      q (R.obj K) ≫ G'.map (adj.counit.app K))
    (hbeta0 : F0'.map beta0 ≫ adj0'.counit.app (G0'.obj (U.obj K)) =
      q0 (R0.obj (U.obj K)) ≫ G0'.map (adj0.counit.app (U.obj K))) :
    beta ≫ b'.hom.app (G'.obj K) =
      src.hom.app K ≫ T'.map (beta0 ≫ R0'.map (dG.hom.app K)) := by
  rw [hsrc]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.id_comp]
  let E := G'.obj K
  let d := dG.hom.app K
  let s := G.map (b.hom.app K) ≫ aG.hom.app (R0.obj (U.obj K))
  let rhs := s ≫ T'.map (beta0 ≫ R0'.map d)
  let ev := aF'.hom.app (R0'.obj (U'.obj E)) ≫
    V'.map (adj0'.counit.app (U'.obj E)) ≫ e' E
  have hce := hc' E
  change F'.map (b'.hom.app E) ≫ ev = adj'.counit.app E at hce
  have hd : F0'.map (beta0 ≫ R0'.map d) ≫ adj0'.counit.app (U'.obj E) =
      (q0 (R0.obj (U.obj K)) ≫ G0'.map (adj0.counit.app (U.obj K))) ≫ d := by
    exact (counit_postcompose adj0' beta0 d).trans (congrArg (fun t ↦ t ≫ d) hbeta0)
  have heval : F'.map rhs ≫ ev = q (R.obj K) ≫ G'.map (adj.counit.app K) := by
    dsimp only [rhs, ev]
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% aF'.hom.naturality (beta0 ≫ R0'.map d)]
    rw [← V'.map_comp_assoc]
    rw [hd]
    simp only [Functor.map_comp, Category.assoc]
    dsimp only [s]
    rw [reassoc_of% hsquare (R.obj K) (R0.obj (U.obj K)) (b.hom.app K)]
    rw [← reassoc_of% aG'.hom.naturality (adj0.counit.app (U.obj K))]
    rw [hcancel K]
    simp only [← G'.map_comp]
    rw [hc K]
  change beta ≫ b'.hom.app E = rhs
  apply mate_coordinate_ext adj' b' ev beta rhs hce
  exact heval.trans hbeta.symm

/-- The bare base-change mate commutes with the explicitly constructed coordinate
isomorphisms. This only concerns the pulled-back coefficient object, with no chosen
coefficient morphism or second coefficient object.

Proof: let c and i be the comparisons selected by exists_derivedPullbackComposition,
and let a be the adjunctions pinned to their derived counits. The equivalence for
inverse spectrum pullback is built from c and i. The direct-image coordinate iso
is the conjugate of affineSpectrumDerivedPullbackIso, under a(f) composed with the
inverse spectrum equivalence on X and the inverse spectrum equivalence on S
composed with a(f0). Its counit equation is conjugateEquiv_counit. First postcompose
both sides with the inverse direct-image coordinate map and cancel its hom-inverse
pair. Apply the inverse Hom equivalence of a(fprime) to this equation. Expand both
base-change
maps into their square comparison followed by pullback of the counit. Substitute
the conjugate counit equations for f and fprime. Naturality moves the inserted
spectrum equivalence units across the square comparisons. The associativity law
for c, applied to the four spectrum naturality squares, identifies the two square
comparison composites. The unit laws for c and the triangle identities for the
spectrum equivalences cancel the inverse spectrum maps and leave identical
transposes. Injectivity of a(fprime)'s Hom equivalence proves the displayed
identity. The equivalence construction retains the specified counit, so this
calculation uses the actual comparisons defining the data, not arbitrary isos.
It needs only commutativity of the two squares; empty schemes, zero rings and
zero coefficient objects are included in the same categorical calculation.
Source: Stacks Project, Tag 08HY, counit definition of the comparison; Tag 0D5S,
composition and its unit and associativity identities.
(blueprint: lem-pc-affine-spectrum-mate-compatibility). -/
theorem affineSpectrum_baseChange_mate_compatibility
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (h0 : Spec.map g'.appTop ≫ Spec.map f.appTop =
      Spec.map f'.appTop ≫ Spec.map g.appTop)
    (K : schemeDerivedCategory X) :
    schemeDerivedBaseChangeMap f f' g g' h K ≫
        (affineSpectrumDerivedDirectImageIso f').hom.app ((derivedPullback g').obj K) =
      (affineSpectrumBaseChangeSourceIso f g).hom.app K ≫
        (derivedPullback S'.toSpecΓ).map
          (schemeDerivedBaseChangeMap (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) h0
              (affineSpectrumDerivedObject X K) ≫
            (schemeDerivedDirectImage (Spec.map f'.appTop)).map
              ((affineSpectrumDerivedPullbackIso g').hom.app K)) := by
  delta affineSpectrumDerivedObject
  exact coordinate_mate_compatibility
    (derivedPullback f) (schemeDerivedDirectImage f)
    (derivedPullback f') (schemeDerivedDirectImage f')
    (derivedPullback g) (derivedPullback g')
    (derivedPullback (Spec.map f.appTop)) (schemeDerivedDirectImage (Spec.map f.appTop))
    (derivedPullback (Spec.map f'.appTop)) (schemeDerivedDirectImage (Spec.map f'.appTop))
    (derivedPullback (Spec.map g.appTop)) (derivedPullback (Spec.map g'.appTop))
    (derivedPullback X.isoSpec.inv) (derivedPullback X'.isoSpec.inv)
    (derivedPullback X.toSpecΓ) (derivedPullback X'.toSpecΓ)
    (derivedPullback S.toSpecΓ) (derivedPullback S'.toSpecΓ)
    (canonicalSchemeDerivedAdjunction f) (canonicalSchemeDerivedAdjunction f')
    (canonicalSchemeDerivedAdjunction (Spec.map f.appTop))
    (canonicalSchemeDerivedAdjunction (Spec.map f'.appTop))
    (affineSpectrumDerivedDirectImageIso f) (affineSpectrumDerivedDirectImageIso f')
    (affineSpectrumForwardPullbackIso f) (affineSpectrumForwardPullbackIso f')
    (affineSpectrumForwardPullbackIso g) (affineSpectrumForwardPullbackIso g')
    (affineSpectrumDerivedPullbackIso g')
    (affineSpectrumBaseChangeSourceIso f g) rfl
    (affineSpectrumUnitInv X) (affineSpectrumUnitInv X')
    (canonicalDerivedSquareComparison f f' g g' h)
    (canonicalDerivedSquareComparison (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) h0)
    (affineSpectrum_counit_compatibility f) (affineSpectrum_counit_compatibility f')
    (affineSpectrum_comparison_cancellation g')
    (affineSpectrum_pullback_square_coherence f f' g g' h h0)
    K (schemeDerivedBaseChangeMap f f' g g' h K)
    (schemeDerivedBaseChangeMap (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) h0 ((derivedPullback X.isoSpec.inv).obj K))
    (schemeDerivedMate_evaluation f f' g g' h K)
    (schemeDerivedMate_evaluation (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) h0 ((derivedPullback X.isoSpec.inv).obj K))

end AlgebraicGeometry
