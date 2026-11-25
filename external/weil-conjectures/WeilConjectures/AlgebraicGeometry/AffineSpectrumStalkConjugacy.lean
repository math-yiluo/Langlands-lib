/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.AffineSpectrumComparisonSourceTransport

/-! # Pointwise conjugacy for termwise affine spectrum representatives

Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction;
Tag 0098, stalks of pullback, and Tag 0D5S, pullback composition.
(blueprint: lem-pc-affine-spectrum-stalk-conjugacy).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem spectrum_stalkComparison_normalized
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    {K : schemeDerivedCategory X} {K' : schemeDerivedCategory X'}
    {φ : (derivedPullback g').obj K ⟶ K'}
    (c : Coordinates g' K K' φ) (z : X') (i : ℤ) :
    stalkComparison f f' g g' sq c z i ≫
        ((comparisonStalkHomologyIso X' z c.N i).inv ≫
          (comparisonStalkCohomology X' z i).map c.e'.hom) =
      comparisonIntoPullback f f' g g' sq z c.P c.counit_isIso i ≫
        (comparisonStalkCohomology X' z i).map ((derivedPullback g').map c.e.hom ≫ φ) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  have := c.counit_isIso
  have ht := comparisonStalkHomologyIso_naturality X' z c.t i
  have ht' : HomologicalComplex.homologyMap
      (((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
        (.up ℤ)).map c.t) i ≫ (comparisonStalkHomologyIso X' z c.N i).inv =
      (comparisonStalkHomologyIso X' z
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P) i).inv ≫
          (comparisonStalkCohomology X' z i).map (DerivedCategory.Q.map c.t) := by
    apply (cancel_epi (comparisonStalkHomologyIso X' z
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P) i).hom).mp
    rw [← Category.assoc, ← ht]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have ht'' := congrArg (fun a => a ≫ (comparisonStalkCohomology X' z i).map c.e'.hom) ht'
  simp only [Category.assoc] at ht''
  simp only [stalkComparison, comparisonIntoPullback, Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp, ← Functor.map_comp, ← c.represents]
  simp only [cast_eq, Functor.map_comp, IsIso.inv_hom_id_assoc]
  rw [ht'']

private theorem square_of_normalizations
    {D : Type*} [Category D] {U V W Z E G : D}
    (l : U ⟶ V) (a : U ⟶ W) (b : V ⟶ Z) (c : W ⟶ E) (d : Z ⟶ G)
    (x : U ⟶ E) (y : V ⟶ G) (t : E ⟶ G)
    (hc : a ≫ c = x) (hd : b ≫ d = y) (hl : l ≫ y = x ≫ t) :
    l ≫ b ≫ d = a ≫ c ≫ t := by
  rw [hd, hl, ← Category.assoc a, hc]

private theorem postcompose_comparison_transport
    {D : Type*} [Category D] {U V W X Y Z : D}
    {l : U ⟶ V} {p : V ⟶ W} {q : U ⟶ X} {a : X ⟶ Y} {b : Y ⟶ W}
    {c : W ⟶ Z} {d : Y ⟶ Z} {e : X ⟶ Z}
    (hl : l ≫ p = q ≫ a ≫ b) (hbc : b ≫ c = d) (had : a ≫ d = e) :
    l ≫ p ≫ c = q ≫ e := by
  simpa only [Category.assoc, hbc, had] using congrArg (fun k ↦ k ≫ c) hl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The two squares require elaborating distinct nested stalk cohomology models.
/-- Pointwise comparison arrows are conjugate when the spectrum representatives
are the termwise pullbacks. This does not construct such representatives, nor
assert a stalk condition for either square.

Proof: normalize each comparison by the exact-stalk homology isomorphism and
its target representative isomorphism e'. Naturality for the chain map t and the
represents equation give comparisonIntoPullback followed by the derived stalk
cohomology map of L(g')*(e);phi. Apply the source-only affine spectrum transport
with c.P, d.P, c.e, d.e and hP. It gives an additive source isomorphism and a natural
isomorphism T from original derived stalk cohomology to spectrum pullback followed
by spectrum derived stalk cohomology. Postcompose its comparison square with the
spectrum coefficient morphism. The inverse composition comparison cancels the
composition comparison defining affineSpectrumDerivedMorphism. Naturality of T
at phi gives a commuting square for the normalized comparisons. The target
isomorphism is original normalization, then T at K', then inverse spectrum
normalization. Cancel the latter normalization and apply Arrow.isoMk. The target
transport works for arbitrary target representatives, so the retained hypothesis
hN is unnecessary for this argument. No horizontal comparison is assumed invertible.
Source: Stacks Project, Tag 0DJ8, affine reduction and equation-bc;
Tag 0098, tensor-pullback stalk formula; Tag 0D5S, composition of derived pullback.
(blueprint: lem-pc-affine-spectrum-stalk-conjugacy). -/
theorem nonempty_affineSpectrum_stalkComparison_arrow_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (c : Coordinates g' K K' φ)
    (d : Coordinates (Spec.map g'.appTop)
      (affineSpectrumDerivedObject X K) (affineSpectrumDerivedObject X' K')
      (affineSpectrumDerivedMorphism g' K K' φ))
    (hP : d.P = ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj c.P)
    (hN : d.N = ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj c.N)
    (z0 : Spec Γ(X', ⊤)) (i : ℤ) :
    Nonempty
      (Arrow.mk ((forget₂ (ModuleCat.{u} (X'.presheaf.stalk (X'.isoSpec.inv z0)))
          AddCommGrpCat.{u}).map
            (stalkComparison f f' g g' sq c (X'.isoSpec.inv z0) i)) ≅
        Arrow.mk ((forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
          AddCommGrpCat.{u}).map
            (stalkComparison (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 d z0 i))) := by
  have _ := hN
  let z := X'.isoSpec.inv z0
  let H := comparisonStalkCohomology X' z i
  let H0 := comparisonStalkCohomology (Spec Γ(X', ⊤)) z0 i
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
    AddCommGrpCat.{u}
  obtain ⟨T, hT⟩ := exists_affineSpectrum_comparisonIntoPullback_transport
    f f' g g' sq sq0 z0 i
  obtain ⟨l, hl⟩ := hT K c.P d.P c.isKFlat d.isKFlat
    c.counit_isIso d.counit_isIso c.e d.e hP
  let cTarget := (comparisonStalkHomologyIso X' z c.N i).symm ≪≫ H.mapIso c.e'
  let dTarget := (comparisonStalkHomologyIso (Spec Γ(X', ⊤)) z0 d.N i).symm ≪≫
    H0.mapIso d.e'
  let r := (F.mapIso cTarget) ≪≫ T.app K' ≪≫ (F0.mapIso dTarget).symm
  have hc := spectrum_stalkComparison_normalized f f' g g' sq c z i
  have hd := spectrum_stalkComparison_normalized
    (Spec.map f.appTop) (Spec.map f'.appTop) (Spec.map g.appTop)
    (Spec.map g'.appTop) sq0 d z0 i
  have hn := T.hom.naturality φ
  have hphi : (affineSpectrumDerivedPullbackIso g').inv.app K ≫
      affineSpectrumDerivedMorphism g' K K' φ =
      (derivedPullback X'.isoSpec.inv).map φ := by
    simp [affineSpectrumDerivedMorphism]
  have hw : l.hom ≫ F0.map (stalkComparison (Spec.map f.appTop)
        (Spec.map f'.appTop) (Spec.map g.appTop) (Spec.map g'.appTop) sq0 d z0 i) ≫
        (F0.mapIso dTarget).hom =
      F.map (stalkComparison f f' g g' sq c z i) ≫
        (F.mapIso cTarget).hom ≫ (T.app K').hom := by
    change l.hom ≫ F0.map (stalkComparison (Spec.map f.appTop)
        (Spec.map f'.appTop) (Spec.map g.appTop) (Spec.map g'.appTop) sq0 d z0 i) ≫
        F0.map dTarget.hom =
      F.map (stalkComparison f f' g g' sq c z i) ≫
        F.map cTarget.hom ≫ T.hom.app K'
    have hc' : stalkComparison f f' g g' sq c z i ≫ cTarget.hom =
        comparisonIntoPullback f f' g g' sq z c.P c.counit_isIso i ≫
          H.map ((derivedPullback g').map c.e.hom ≫ φ) := hc
    have hd' : stalkComparison (Spec.map f.appTop) (Spec.map f'.appTop)
        (Spec.map g.appTop) (Spec.map g'.appTop) sq0 d z0 i ≫ dTarget.hom =
      comparisonIntoPullback (Spec.map f.appTop) (Spec.map f'.appTop)
        (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 d.P d.counit_isIso i ≫
          H0.map ((derivedPullback (Spec.map g'.appTop)).map d.e.hom ≫
            affineSpectrumDerivedMorphism g' K K' φ) := hd
    have hcF := congrArg F.map hc'
    have hdF := congrArg F0.map hd'
    simp only [Functor.map_comp] at hcF hdF
    have hk := congrArg (fun a => F0.map (H0.map a)) hphi
    simp only [Functor.map_comp] at hk
    have hn' : T.hom.app ((derivedPullback g').obj K) ≫
        F0.map (H0.map ((derivedPullback X'.isoSpec.inv).map φ)) =
      F.map (H.map φ) ≫ T.hom.app K' := hn.symm
    have hl' := postcompose_comparison_transport hl hk hn'
    simp only [Functor.map_comp, Category.assoc] at hl'
    exact square_of_normalizations l.hom _ _ _ _ _ _ _ hcF hdF
      (by simpa only [Category.assoc] using hl')
  refine ⟨Arrow.isoMk l r ?_⟩
  change l.hom ≫ F0.map (stalkComparison (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 d z0 i) =
    F.map (stalkComparison f f' g g' sq c z i) ≫ r.hom
  apply (cancel_mono (F0.mapIso dTarget).hom).mp
  simpa only [r, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using hw


end AlgebraicGeometry.SingleComplexBaseChange
