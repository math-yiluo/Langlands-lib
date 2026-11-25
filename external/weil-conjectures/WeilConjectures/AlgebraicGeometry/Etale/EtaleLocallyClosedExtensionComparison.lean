/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp

/-!
# Étale extension by zero for locally closed immersions

Source: literature/stacks-project/etale-cohomology.tex, Tag 0GJ1
(blueprint: lem-sfb-etale-locally-closed-extension-comparison).

The finite-open comparison is stated for the canonical pullback square.  The
closure-defined extension uses the scheme-theoretic image and its canonical
open factor.  Its factorization and closed-immersion compatibilities are
recorded as natural-isomorphism existence statements.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- The closure-defined étale extension associated to a quasi-compact immersion.

Source: Stacks Project, Morphisms, Tags 01R6--01R8
(blueprint: lem-sfb-etale-locally-closed-extension-comparison). It is the composite of
extension by zero along `a.toImage` and direct image along `a.imageι`.
-/
noncomputable def etaleLocallyClosedExtension
    {A : Type (u + 1)} [CommRing A]
    {S X : Scheme.{u}} (a : S ⟶ X) [IsImmersion a]
    (hqa : QuasiCompact a) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) := by
  letI : QuasiCompact a := hqa
  exact Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) a.toImage ⋙
    Etale.lowerStar (ModuleCat.{u + 1} A) a.imageι

/-- The canonical restriction normalization for the closure-defined extension.

Source: literature/stacks-project/etale-cohomology.tex, Tags 0F70 and 04CA;
Morphisms, Tags 01R6--01R8
(blueprint: lem-sfb-etale-locally-closed-extension-comparison).

This is the inverse of the open-extension unit, followed by the closed
pushforward counit, with the pullback composition comparison for
`a = a.toImage ≫ a.imageι`. -/
noncomputable def etaleLocallyClosedExtensionRestrictionIso
    {A : Type (u + 1)} [CommRing A]
    {S X : Scheme.{u}} (a : S ⟶ X) [IsImmersion a]
    (hqa : QuasiCompact a) :
    etaleLocallyClosedExtension (A := A) a hqa ⋙ Etale.upperStar (ModuleCat.{u + 1} A) a ≅
      𝟭 (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  letI : QuasiCompact a := hqa
  let L := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) a.toImage
  let R := Etale.lowerStar (ModuleCat.{u + 1} A) a.imageι
  let P := Etale.upperStar (ModuleCat.{u + 1} A) a
  let Q := Etale.upperStar (ModuleCat.{u + 1} A) a.imageι
  let T := Etale.upperStar (ModuleCat.{u + 1} A) a.toImage
  let ecomp := Etale.upperStarComp (ModuleCat.{u + 1} A) a.toImage a.imageι
    a (Scheme.Hom.toImage_imageι a).symm
  exact
    Functor.associator L R P ≪≫
      Functor.isoWhiskerLeft L (
        Functor.isoWhiskerLeft R ecomp ≪≫
          (Functor.associator R Q T).symm ≪≫
          Functor.isoWhiskerRight
            (asIso (Etale.upperStarLowerStarAdjunction
              (ModuleCat.{u + 1} A) a.imageι).counit) T ≪≫
          Functor.leftUnitor T) ≪≫
      (asIso (Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) a.toImage).unit).symm

/-- The canonical restriction normalization for a closed-then-open factorization.

Source: literature/stacks-project/etale-cohomology.tex, Tags 0F70, 04CA and 0GJ1
(blueprint: lem-sfb-etale-locally-closed-extension-comparison).

The two adjunction units/counits and the pullback composition comparison specify
the restriction to the identity on the locally closed source. -/
noncomputable def etaleFactorizationRestrictionIso
    {A : Type (u + 1)} [CommRing A]
    {S W X : Scheme.{u}} (a : S ⟶ X)
    (h : S ⟶ W) (u : W ⟶ X)
    [IsClosedImmersion h] [IsOpenImmersion u]
    (ha : h ≫ u = a) :
    (Etale.lowerStar (ModuleCat.{u + 1} A) h ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) u) ⋙
      Etale.upperStar (ModuleCat.{u + 1} A) a ≅
      𝟭 (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  let F := Etale.lowerStar (ModuleCat.{u + 1} A) h
  let G := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) u
  let P := Etale.upperStar (ModuleCat.{u + 1} A) a
  let Q := Etale.upperStar (ModuleCat.{u + 1} A) u
  let T := Etale.upperStar (ModuleCat.{u + 1} A) h
  let ecomp := Etale.upperStarComp (ModuleCat.{u + 1} A) h u a ha.symm
  exact
    Functor.associator F G P ≪≫
      Functor.isoWhiskerLeft F (
        Functor.isoWhiskerLeft G ecomp ≪≫
          (Functor.associator G Q T).symm ≪≫
          Functor.isoWhiskerRight
            (asIso (Etale.openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) u).unit).symm T ≪≫
          Functor.leftUnitor T) ≪≫
      asIso (Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) h).counit

/-- The canonical restriction normalization after a further closed immersion.

Source: literature/stacks-project/etale-cohomology.tex, Tags 0F70 and 04CA;
Morphisms, Tags 01R6--01R8
(blueprint: lem-sfb-etale-locally-closed-extension-comparison).
It uses pullback composition, the closed counit for `i`, and the closure normalization
for `b`. -/
noncomputable def etaleClosedCompositionRestrictionIso
    {A : Type (u + 1)} [CommRing A]
    {S Y X : Scheme.{u}} (a : S ⟶ X) (b : S ⟶ Y) (i : Y ⟶ X)
    [IsClosedImmersion i] [IsImmersion b]
    (hqb : QuasiCompact b) (ha : b ≫ i = a) :
    (etaleLocallyClosedExtension (A := A) b hqb ⋙
        Etale.lowerStar (ModuleCat.{u + 1} A) i) ⋙
      Etale.upperStar (ModuleCat.{u + 1} A) a ≅
      𝟭 (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) := by
  let E := etaleLocallyClosedExtension (A := A) b hqb
  let F := Etale.lowerStar (ModuleCat.{u + 1} A) i
  let P := Etale.upperStar (ModuleCat.{u + 1} A) a
  let Q := Etale.upperStar (ModuleCat.{u + 1} A) i
  let T := Etale.upperStar (ModuleCat.{u + 1} A) b
  let ecomp := Etale.upperStarComp (ModuleCat.{u + 1} A) b i a ha.symm
  exact
    Functor.associator E F P ≪≫
      Functor.isoWhiskerLeft E (
        Functor.isoWhiskerLeft F ecomp ≪≫
          (Functor.associator F Q T).symm ≪≫
          Functor.isoWhiskerRight
            (asIso (Etale.upperStarLowerStarAdjunction
              (ModuleCat.{u + 1} A) i).counit) T ≪≫
          Functor.leftUnitor T) ≪≫
      etaleLocallyClosedExtensionRestrictionIso (A := A) b hqb

/-- A fully faithful extension with a restriction left inverse detects equality of normalized
comparisons. This is the elementary full-faithfulness argument in Stacks Tag 04CA. -/
private theorem normalized_iso_unique
    {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) (R : D ⥤ C) [F.Full] [F.Faithful]
    (α : F ⋙ R ≅ 𝟭 C) (β : G ⋙ R ≅ 𝟭 C)
    (e e' : F ≅ G)
    (he : Functor.isoWhiskerRight e R ≪≫ β = α)
    (he' : Functor.isoWhiskerRight e' R ≪≫ β = α) : e' = e := by
  have hr : Functor.isoWhiskerRight e' R = Functor.isoWhiskerRight e R := by
    apply Iso.ext
    exact (cancel_mono β.hom).mp (congrArg Iso.hom (he'.trans he.symm))
  apply Iso.ext
  ext X
  let f : F.obj X ⟶ F.obj X := e'.hom.app X ≫ e.inv.app X
  have hf : R.map f = 𝟙 _ := by
    simpa [f] using congrArg (fun t ↦ t ≫ R.map (e.inv.app X))
      (congrArg (fun t ↦ t.hom.app X) hr)
  have hp : F.preimage f = 𝟙 X := by
    apply (cancel_epi (α.hom.app X)).mp
    calc
      α.hom.app X ≫ F.preimage f = R.map (F.map (F.preimage f)) ≫ α.hom.app X :=
        (α.hom.naturality (F.preimage f)).symm
      _ = α.hom.app X ≫ 𝟙 X := by rw [F.map_preimage, hf]; simp
  have hfid : f = 𝟙 _ := by
    simpa using congrArg F.map hp
  exact (cancel_mono (e.inv.app X)).mp (by simpa [f] using hfid)

/-- Normalize an existing comparison by the induced automorphism of the identity functor.
Naturality of its restriction identification verifies the normalization equation. -/
private theorem normalized_iso_exists
    {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) (R : D ⥤ C)
    (α : F ⋙ R ≅ 𝟭 C) (β : G ⋙ R ≅ 𝟭 C) (e₀ : F ≅ G) :
    ∃ e : F ≅ G, Functor.isoWhiskerRight e R ≪≫ β = α := by
  let γ := Functor.isoWhiskerRight e₀ R ≪≫ β
  let τ := γ.symm ≪≫ α
  let θ := (Functor.leftUnitor F).symm ≪≫
    Functor.isoWhiskerRight τ F ≪≫ Functor.leftUnitor F
  refine ⟨θ ≪≫ e₀, ?_⟩
  apply Iso.ext
  ext X
  change R.map (θ.hom.app X ≫ e₀.hom.app X) ≫ β.hom.app X = α.hom.app X
  rw [R.map_comp, Category.assoc]
  have hθ : θ.hom.app X = F.map (τ.hom.app X) := by simp [θ]
  rw [hθ]
  change (F ⋙ R).map (τ.hom.app X) ≫ γ.hom.app X = α.hom.app X
  calc
    _ = γ.hom.app X ≫ τ.hom.app X := γ.hom.naturality (τ.hom.app X)
    _ = _ := by simp [τ]

/-- Restricting the scheme-theoretic image to a closed-then-open factorization recovers
its closed factor, by the kernel form of image base change (Stacks Tags 01R6--01R8). -/
private theorem closure_factorization_square
    {S W X : Scheme.{u}} (a : S ⟶ X) [IsImmersion a] [QuasiCompact a]
    (h : S ⟶ W) (j : W ⟶ X) [IsClosedImmersion h] [IsOpenImmersion j]
    (ha : h ≫ j = a) : IsPullback a.toImage h a.imageι j := by
  have sq : IsPullback (𝟙 S) h a j :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa using ha.symm⟩
  apply (isPullback_of_isClosedImmersion h a.imageι a.toImage j
    (by simpa using ha) ?_).flip
  simpa only [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι] using
    (Scheme.Hom.ker_of_isPullback a j sq).symm

/-- Invert finite/open interchange for the cartesian closure square (Stacks Tag 0GJ1). -/
private theorem closure_factorization_iso
    {A : Type (u + 1)} [CommRing A]
    {S W X : Scheme.{u}} (a : S ⟶ X) [IsImmersion a] (hqa : QuasiCompact a)
    (h : S ⟶ W) (j : W ⟶ X) [IsClosedImmersion h] [IsOpenImmersion j]
    (ha : h ≫ j = a) :
    Nonempty (etaleLocallyClosedExtension (A := A) a hqa ≅
      Etale.lowerStar (ModuleCat.{u + 1} A) h ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j) := by
  let : QuasiCompact a := hqa
  have sq := closure_factorization_square a h j ha
  have := Etale.isIso_finiteOpenComparison (ModuleCat.{u + 1} A) sq
  exact ⟨(asIso (Etale.finiteOpenComparison (ModuleCat.{u + 1} A) sq)).symm⟩

/-- The closures in two closed ambient schemes have equal ideals over the larger ambient
scheme. Transport extension by zero along their unique isomorphism and compose direct images.
Source: Stacks Tags 01R6--01R8 and the direct-image formula. -/
private theorem closure_closed_composition_iso
    {A : Type (u + 1)} [CommRing A]
    {S Y X : Scheme.{u}} (a : S ⟶ X) [IsImmersion a] (hqa : QuasiCompact a)
    (b : S ⟶ Y) [IsImmersion b] (hqb : QuasiCompact b)
    (i : Y ⟶ X) [IsClosedImmersion i] (ha : b ≫ i = a) :
    Nonempty (etaleLocallyClosedExtension (A := A) b hqb ⋙
      Etale.lowerStar (ModuleCat.{u + 1} A) i ≅
        etaleLocallyClosedExtension (A := A) a hqa) := by
  let : QuasiCompact a := hqa
  let : QuasiCompact b := hqb
  have hk : a.imageι.ker = (b.imageι ≫ i).ker := by
    calc
      a.imageι.ker = a.ker := Scheme.IdealSheafData.ker_subschemeι _
      _ = (b.toImage ≫ (b.imageι ≫ i)).ker := by rw [← Category.assoc,
        Scheme.Hom.toImage_imageι, ha]
      _ = (b.imageι ≫ i).ker :=
        Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant _ _
  let q := IsClosedImmersion.lift a.imageι (b.imageι ≫ i) hk.le
  have hq : q ≫ a.imageι = b.imageι ≫ i := IsClosedImmersion.lift_fac _ _ _
  have : IsIso q := IsClosedImmersion.isIso_lift _ _ hk
  have hj : b.toImage ≫ q = a.toImage := by
    rw [← cancel_mono a.imageι, Category.assoc, hq, ← Category.assoc,
      Scheme.Hom.toImage_imageι, ha, Scheme.Hom.toImage_imageι]
  let M := ModuleCat.{u + 1} A
  let eq : Etale.lowerStar M q ≅ Etale.openImmersionLowerShriek M q :=
    (Etale.upperStarInvIsoLowerStarHom M (asIso q)).symm ≪≫
      Etale.upperStarIsoOpenImmersionLowerShriekInv M (asIso q).symm
  refine ⟨?_⟩
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Etale.openImmersionLowerShriek M b.toImage)
      (Etale.lowerStarComp M b.imageι i _ hq ≪≫ (Etale.lowerStarComp M q a.imageι).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      (Etale.openImmersionLowerShriek M b.toImage) eq ≪≫
      (Etale.openImmersionLowerShriekComp M b.toImage q).symm ≪≫
      eqToIso (by congr 1))
      (Etale.lowerStar M a.imageι)

/-- Étale closed/open interchange and closure-defined extension by zero.

Source: literature/stacks-project/etale-cohomology.tex, Tag 0GJ1,
lemma-compatible-shriek-push-finite, together with Morphisms, Tags 01R6--01R8
(blueprint: lem-sfb-etale-locally-closed-extension-comparison).

Proof route. (1) Closed immersions are finite, so
`Etale.isIso_finiteOpenComparison` applied to
`IsPullback.of_hasPullback g u` proves the first conjunct.  By the definition
of `Etale.finiteOpenComparison`, its map is the transpose under
`u_! ⊣ u^*` of the inverse of the exchange map
`u^* g_* v_! L ≅ h_* v^* v_! L ≅ h_* L`.
(2) This comparison is linear over the constant finite ring: naturality under
scalar endomorphisms gives linearity on sections, and the module adjunction
has the same units and counits as the underlying abelian adjunction.
(3) A locally closed immersion into a Noetherian scheme is quasi-compact and
quasi-separated; the same holds after passing to a closed ambient subscheme.
The scheme-theoretic image therefore supplies the open factor `a.toImage` and
closed factor `a.imageι`.
(4) The restriction of the image square to an open factorization is the
cartesian square obtained from `S ×_X W ≅ S`; the scheme-image restriction and
closed-image lemmas identify its closed edge with `S`.
(5) The inverse finite-open comparison gives an initial factorization comparison.
To normalize any comparison `e₀ : F ≅ G`, write `R = a^*` and let
`α : F ⋙ R ≅ 𝟭` and `β : G ⋙ R ≅ 𝟭` be the displayed restriction helpers.
Set `γ = (e₀ ▷ R) ≪≫ β` and `τ = γ.symm ≪≫ α`. Whiskering the automorphism
`τ` of the identity with `F` gives `θ : F ≅ F`; then `θ ≪≫ e₀` is normalized,
by naturality of `γ`. For uniqueness, if two comparisons agree after `R`, their
quotient is an endomorphism of `F`. Fullness lifts it to the source, and the
restriction identification `α` shows that lift is the identity. Faithfulness
then identifies the two comparisons. The extension `F` is fully faithful since
open extension and closed direct image are fully faithful.
(6) For `b : S ⟶ Y` and closed `i : Y ⟶ X`, scheme-theoretic density of
`b.toImage` gives `a.imageι.ker = (b.imageι ≫ i).ker`. The closed-immersion
lift for this equality is an isomorphism `q : b.image ≅ a.image` over `X`.
Its compatibility with the open factors follows by canceling `a.imageι`.
(7) Direct images compose by `Etale.lowerStarComp`. For the isomorphism `q`,
direct image equals open extension: both identify with inverse pullback.
Composition of open extensions then identifies the two closure extensions.
Apply the normalization and uniqueness argument of step (5), now using
`etaleClosedCompositionRestrictionIso`. All constructions are already for
`ModuleCat A`, so no separate passage from abelian sheaves is needed.
-/
theorem etale_locallyClosed_extension_comparison
    {A : Type (u + 1)} [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X]
    {Z W : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (u : W ⟶ X) [IsOpenImmersion u] :
    IsIso (Etale.finiteOpenComparison (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback g u)) ∧
      ∀ {S : Scheme.{u}} (a : S ⟶ X) [IsImmersion a],
        ∃ hqa : QuasiCompact a,
          (∀ {W' : Scheme.{u}} (h : S ⟶ W') (u' : W' ⟶ X)
              [IsClosedImmersion h] [IsOpenImmersion u'],
              (ha : h ≫ u' = a) →
              ∃ e : etaleLocallyClosedExtension (A := A) a hqa ≅
                  Etale.lowerStar (ModuleCat.{u + 1} A) h ⋙
                    Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) u',
                  Functor.isoWhiskerRight e (Etale.upperStar (ModuleCat.{u + 1} A) a) ≪≫
                    etaleFactorizationRestrictionIso (A := A) a h u' ha =
                  etaleLocallyClosedExtensionRestrictionIso (A := A) a hqa ∧
                ∀ e' : etaleLocallyClosedExtension (A := A) a hqa ≅
                    Etale.lowerStar (ModuleCat.{u + 1} A) h ⋙
                      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) u',
                  Functor.isoWhiskerRight e' (Etale.upperStar (ModuleCat.{u + 1} A) a) ≪≫
                      etaleFactorizationRestrictionIso (A := A) a h u' ha =
                    etaleLocallyClosedExtensionRestrictionIso (A := A) a hqa →
                  e' = e) ∧
          (∀ {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
              (b : S ⟶ Y) [IsImmersion b],
              (ha : b ≫ i = a) →
              ∃ hqb : QuasiCompact b,
                ∃ e : etaleLocallyClosedExtension (A := A) b hqb ⋙
                    Etale.lowerStar (ModuleCat.{u + 1} A) i ≅
                      etaleLocallyClosedExtension (A := A) a hqa,
                  Functor.isoWhiskerRight e (Etale.upperStar (ModuleCat.{u + 1} A) a) ≪≫
                      etaleLocallyClosedExtensionRestrictionIso (A := A) a hqa =
                      etaleClosedCompositionRestrictionIso (A := A) a b i hqb ha ∧
                  ∀ e' : etaleLocallyClosedExtension (A := A) b hqb ⋙
                      Etale.lowerStar (ModuleCat.{u + 1} A) i ≅
                        etaleLocallyClosedExtension (A := A) a hqa,
                    Functor.isoWhiskerRight e' (Etale.upperStar (ModuleCat.{u + 1} A) a) ≪≫
                        etaleLocallyClosedExtensionRestrictionIso (A := A) a hqa =
                      etaleClosedCompositionRestrictionIso (A := A) a b i hqb ha →
                    e' = e) := by
  refine ⟨Etale.isIso_finiteOpenComparison (ModuleCat.{u + 1} A)
    (IsPullback.of_hasPullback g u), ?_⟩
  intro S a _
  have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  have hqa : QuasiCompact a := inferInstance
  refine ⟨hqa, ?_, ?_⟩
  · intro W' h j _ _ ha
    obtain ⟨e₀⟩ := closure_factorization_iso (A := A) a hqa h j ha
    let : QuasiCompact a := hqa
    have : (etaleLocallyClosedExtension (A := A) a hqa).Full := by
      dsimp [etaleLocallyClosedExtension]
      infer_instance
    have : (etaleLocallyClosedExtension (A := A) a hqa).Faithful := by
      dsimp [etaleLocallyClosedExtension]
      infer_instance
    obtain ⟨e, he⟩ := normalized_iso_exists _ _ _
      (etaleLocallyClosedExtensionRestrictionIso (A := A) a hqa)
      (etaleFactorizationRestrictionIso (A := A) a h j ha) e₀
    exact ⟨e, he, fun e' he' ↦ normalized_iso_unique _ _ _ _ _ e e' he he'⟩
  · intro Y i _ b _ ha
    have hqb : QuasiCompact b := inferInstance
    obtain ⟨e₀⟩ := closure_closed_composition_iso (A := A) a hqa b hqb i ha
    let : QuasiCompact b := hqb
    have : (etaleLocallyClosedExtension (A := A) b hqb ⋙
        Etale.lowerStar (ModuleCat.{u + 1} A) i).Full := by
      dsimp [etaleLocallyClosedExtension]
      infer_instance
    have : (etaleLocallyClosedExtension (A := A) b hqb ⋙
        Etale.lowerStar (ModuleCat.{u + 1} A) i).Faithful := by
      dsimp [etaleLocallyClosedExtension]
      infer_instance
    obtain ⟨e, he⟩ := normalized_iso_exists _ _ _
      (etaleClosedCompositionRestrictionIso (A := A) a b i hqb ha)
      (etaleLocallyClosedExtensionRestrictionIso (A := A) a hqa) e₀
    exact ⟨hqb, e, he, fun e' he' ↦ normalized_iso_unique _ _ _ _ _ e e' he he'⟩

end AlgebraicGeometry
