/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenMateResolutionNormalization

/-! # The open direct-image mate of the fixed pullback comparison

Source: Stacks Project, Cohomology, Tags 08FE, 079W and 0D5S.
(blueprint: lem-pc-perfect-hom-open-comparison-mate-is-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem openMateAdjunctionTransport {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'}
    (a₀ a : L ⊣ R) (a₀' a' : L' ⊣ R')
    (κ : G ⋙ L' ≅ L ⋙ H) (τ : G ≅ G) (β : R ⋙ G ≅ H ⋙ R')
    (E : D)
    (h : L'.map (β.hom.app E) ≫ a₀'.counit.app (H.obj E) =
      κ.hom.app (R.obj E) ≫ H.map (a₀.counit.app E)) :
    let c := (conjugateIsoEquiv a a₀) (Iso.refl _)
    let c' := (conjugateIsoEquiv a₀' a') (Iso.refl _)
    let γ := Functor.isoWhiskerRight c G ≪≫ Functor.isoWhiskerLeft R τ ≪≫
      β ≪≫ Functor.isoWhiskerLeft H c'
    L'.map (γ.hom.app E) ≫ a'.counit.app (H.obj E) =
      L'.map (τ.hom.app (R.obj E)) ≫ κ.hom.app (R.obj E) ≫ H.map (a.counit.app E) := by
  dsimp only
  let c := (conjugateIsoEquiv a a₀) (Iso.refl _)
  let c' := (conjugateIsoEquiv a₀' a') (Iso.refl _)
  have hc : L.map (c.hom.app E) ≫ a₀.counit.app E = a.counit.app E := by
    simpa only [c, conjugateIsoEquiv_apply_hom, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp] using
      conjugateEquiv_counit a a₀ (𝟙 L) E
  have hc' : L'.map (c'.hom.app (H.obj E)) ≫ a'.counit.app (H.obj E) =
      a₀'.counit.app (H.obj E) := by
    simpa only [c', conjugateIsoEquiv_apply_hom, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp] using
      conjugateEquiv_counit a₀' a' (𝟙 L') (H.obj E)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  change L'.map (G.map (c.hom.app E)) ≫ L'.map (τ.hom.app (R.obj E)) ≫
    L'.map (β.hom.app E) ≫ L'.map (c'.hom.app (H.obj E)) ≫
    a'.counit.app (H.obj E) = _
  rw [hc', h]
  rw [← L'.map_comp_assoc, τ.hom.naturality (c.hom.app E), L'.map_comp_assoc]
  have hn := κ.hom.naturality (c.hom.app E)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← H.map_comp, hc]


private theorem openMateSuppliedCounit
    {S Y T : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (ap : derivedPullback (pullback.fst s r) ⊣
      schemeDerivedDirectImage (pullback.fst s r))
    (ap' : derivedPullback (pullback.fst (B.ι ≫ s) r) ⊣
      schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r))
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (pullback s r).toRingedSpace)) ℤ)
    [I.IsKInjective] :
    let b := perfectHomOpenMap s B r
    let σ : schemeMVDerivedRestriction Y B ≅ derivedPullback B.ι :=
      (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
    let he : b ≫ pullback.fst s r = pullback.fst (B.ι ≫ s) r ≫ B.ι := by
      simp [b, perfectHomOpenMap, pullback.map]
    let κ := perfectHomComposition b (pullback.fst s r) ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) he) ≪≫
      (perfectHomComposition (pullback.fst (B.ι ≫ s) r) B.ι).symm ≪≫
      Functor.isoWhiskerRight σ.symm (derivedPullback (pullback.fst (B.ι ≫ s) r))
    (derivedPullback (pullback.fst (B.ι ≫ s) r)).map
        ((perfectHomOpenSuppliedComparison s B r a ap ap').hom.app
          (DerivedCategory.Q.obj I)) ≫
        ap'.counit.app ((derivedPullback b).obj (DerivedCategory.Q.obj I)) =
      κ.inv.app ((schemeDerivedDirectImage (pullback.fst s r)).obj
        (DerivedCategory.Q.obj I)) ≫
        (derivedPullback b).map (ap.counit.app (DerivedCategory.Q.obj I)) := by
  classical
  dsimp only
  let a₀ := canonicalPullbackAdjunction B.ι
  let ap₀ := canonicalPullbackAdjunction (pullback.fst s r)
  let ap₀' := canonicalPullbackAdjunction (pullback.fst (B.ι ≫ s) r)
  let σ := (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
  let σ₀ := (conjugateIsoEquiv a₀ (schemeMVAdjunction Y B)).symm (Iso.refl _)
  let κ := perfectHomComposition (perfectHomOpenMap s B r) (pullback.fst s r) ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback f) (perfectHomOpenSquare s B r).w.symm) ≪≫
    (perfectHomComposition (pullback.fst (B.ι ≫ s) r) B.ι).symm ≪≫
    Functor.isoWhiskerRight σ₀.symm (derivedPullback (pullback.fst (B.ι ≫ s) r))
  have h := openMateAdjunctionTransport ap₀ ap ap₀' ap' κ.symm (σ ≪≫ σ₀.symm)
    (perfectHomOpenDerivedComparison s B r) (DerivedCategory.Q.obj I)
    (perfectHomOpenComparison_counit_resolution s B r I)
  change _ = _ at h
  simp only [perfectHomOpenSuppliedComparison, κ, σ, σ₀, a₀, ap₀, ap₀',
    Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.trans_hom, Functor.map_comp, Category.assoc] at h ⊢
  simpa only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, Category.id_comp, Category.comp_id] using h


/-- The right mate of the fixed open pullback square is invertible, independently
of the testing and coefficient objects.

Source: Stacks Project, Cohomology, Lemma 20.32.4 (Tag 08FE),
Lemma 20.28.1 (Tag 079W), and Lemma 20.27.2 (Tag 0D5S).
(blueprint: lem-pc-perfect-hom-open-comparison-mate-is-iso).

Proof: Put pi = pullback.fst s r and pi' = pullback.fst (B.ι ≫ s) r.
The maps b and pi' identify B x_S T with the inverse-image open pi inverse B:
b is an open immersion, and the cartesian universal property supplies inverse
lifts between the two presentations over both Y x_S T and B. The mate is thus
a map Rpi_* followed by restriction to B -> restriction to pi inverse B followed
by Rpi'_* (with the latter restriction presented as Lb*).
For the derived adjunctions induced by the tensor-pullback adjunctions and their
specified derived comparison maps, this mate is the derived sectionwise identity
of Tag 08FE. To check its normalization, evaluate the composition comparison on
a K-flat complex: its defining left-derived counit equation is the ordinary
pullback composition comparison. Transpose by the derived adjunctions, whose
Hom equivalences on localized underived maps are pinned by the ordinary tensor
adjunction. This gives the ordinary direct-image/restriction map on complexes.
Choose a K-injective representative I of a target object. Restriction of I to
the inverse-image open is K-injective by Tag 08BS, and both complexes at an open
W of B have sections I(pi inverse W), with identical differentials. Hence the
mate component is the identity under these comparisons and is invertible.
The derived universal properties extend this identity to all derived objects.
Changing either projection adjunction conjugates its mate by the invertible
right-adjoint uniqueness comparisons. The supplied open adjunction changes
sigma by left-adjoint uniqueness; its whiskered comparison and its mate are
invertible. Thus the assertion holds for every supplied adjunction as stated.
For B empty both functors take values in the zero category; for B top the square
is the identity open square. The same calculation covers these cases and the
zero complex. No flatness, finiteness or quasi-coherence is required. -/
theorem perfect_hom_open_comparison_mate_isIso
    {S Y T : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    :
    let b := pullback.map (B.ι ≫ s) r s r B.ι (𝟙 T) (𝟙 S) (by simp) (by simp)
    let σ : schemeMVDerivedRestriction Y B ≅ derivedPullback B.ι :=
      (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
    let he : b ≫ pullback.fst s r = pullback.fst (B.ι ≫ s) r ≫ B.ι := by
      simp [b, pullback.map]
    let κ₀ := perfectHomComposition b (pullback.fst s r) ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) he) ≪≫
      (perfectHomComposition (pullback.fst (B.ι ≫ s) r) B.ι).symm ≪≫
      Functor.isoWhiskerRight σ.symm (derivedPullback (pullback.fst (B.ι ≫ s) r))
    ∀ (ap : derivedPullback (pullback.fst s r) ⊣
        schemeDerivedDirectImage (pullback.fst s r))
      (ap' : derivedPullback (pullback.fst (B.ι ≫ s) r) ⊣
        schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) r)),
      IsIso (mateEquiv ap ap' (TwoSquare.mk _ _ _ _ κ₀.inv)) := by
  classical
  dsimp only
  intro ap ap'
  let β := perfectHomOpenSuppliedComparison s B r a ap ap'
  let α := (mateEquiv ap ap' (TwoSquare.mk _ _ _ _
    (perfectHomComposition (perfectHomOpenMap s B r) (pullback.fst s r) ≪≫
      eqToIso (congrArg (fun f ↦ derivedPullback f) (perfectHomOpenSquare s B r).w.symm)
        ≪≫ (perfectHomComposition (pullback.fst (B.ι ≫ s) r) B.ι).symm ≪≫
      Functor.isoWhiskerRight
        ((conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)).symm
        (derivedPullback (pullback.fst (B.ι ≫ s) r))).inv))
  change IsIso α
  have hQ (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (pullback s r).toRingedSpace)) ℤ)
      [I.IsKInjective] : α.app (DerivedCategory.Q.obj I) =
        β.hom.app (DerivedCategory.Q.obj I) := by
    apply (ap'.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_symm_apply]
    exact (mateEquiv_counit ap ap' _ (DerivedCategory.Q.obj I)).trans
      (openMateSuppliedCounit s B r a ap ap' I).symm
  have hE (E : schemeDerivedCategory (pullback s r)) : α.app E = β.hom.app E := by
    let I := schemeMVResolution (pullback s r) E
    let e := schemeMVResolutionIso (pullback s r) E
    apply (cancel_epi ((schemeDerivedDirectImage (pullback.fst s r) ⋙
      schemeMVDerivedRestriction Y B).map e.hom)).mp
    rw [α.naturality, β.hom.naturality, hQ I]
  have (E : schemeDerivedCategory (pullback s r)) : IsIso (α.app E) := by
    rw [hE E]
    infer_instance
  exact NatIso.isIso_of_isIso_app α

end AlgebraicGeometry
