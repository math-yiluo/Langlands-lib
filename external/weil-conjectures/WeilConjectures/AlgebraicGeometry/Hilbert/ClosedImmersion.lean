/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Hilbert.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
public import WeilConjectures.RingTheory.DualContent
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# The Hilbert functor of a closed subscheme

Let `i : X ⟶ Y` be a closed immersion and `g : Y ⟶ S`. Pushing closed subschemes forward along
the closed immersions `X ×[S] T ⟶ Y ×[S] T` identifies `Hilb^d_{X/S}` with the subfunctor of
`Hilb^d_{Y/S}` of those `Z ⊆ Y_T` contained in `X_T`. We show that this subfunctor is closed:
for an affine `T` and `Z ∈ Hilb^d_{Y/S}(T)` there is a largest closed subscheme `T_X ⊆ T` over
which `Z` lies in `X_T` (the *closed-immersion claim*, blueprint
`theorem-hilbert-schemes-points-smooth-curve--1`, Step 1). Consequently, if `Hilb^d_{Y/S}` is
representable, so is `Hilb^d_{X/S}`.

More generally, for any `S`-scheme `T`, any `Z ∈ Hilb^d_{Y/S}(T)` and any closed subscheme
`W ⊆ Y_T`, the locus of `T` over which `Z` lies in `W` is a closed subscheme of `T`. Over an
affine `T` it is cut out by the values of the linear forms on `𝒪_Z` on the ideal of `W`; in
general these local closed subschemes glue.

## Main definitions

- `AlgebraicGeometry.pullbackCompMap`: the closed immersion `X ×[S] T ⟶ Y ×[S] T`.
- `AlgebraicGeometry.hilbertPresheafCompι`: the inclusion `Hilb^d_{X/S} ⟶ Hilb^d_{Y/S}`.

## Main statements

- `AlgebraicGeometry.exists_le_ker_iff_comap_le_of_isAffine`: the locus where `Z` lies in a
  closed subscheme `W ⊆ Y_T` is closed, for an affine base `T`.
- `AlgebraicGeometry.exists_idealSheafData_le_ker_iff_comap_le`: the same for any base `T`.
- `AlgebraicGeometry.exists_le_ker_iff_mem_range_hilbertPresheafCompι`: the closed-immersion
  claim, for an affine base `T`.
- `AlgebraicGeometry.isRepresentable_hilbertPresheaf_of_isClosedImmersion`: if `Hilb^d_{Y/S}`
  is representable, so is `Hilb^d_{X/S}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- The four conditions defining the Hilbert functor are invariant under precomposition with an
isomorphism. -/
lemma isFinite_flat_finrank_iso_comp_iff {Z Z' T : Scheme.{u}} (e : Z' ⟶ Z) [IsIso e] (p : Z ⟶ T)
    (d : ℕ) :
    (IsFinite (e ≫ p) ∧ Flat (e ≫ p) ∧ LocallyOfFinitePresentation (e ≫ p) ∧
      ∀ t, (e ≫ p).finrank t = d) ↔
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ ∀ t, p.finrank t = d := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    have : IsFinite p := (MorphismProperty.cancel_left_of_respectsIso @IsFinite e p).1 h₁
    have : Flat p := (MorphismProperty.cancel_left_of_respectsIso @Flat e p).1 h₂
    refine ⟨‹_›, ‹_›, (MorphismProperty.cancel_left_of_respectsIso
      @LocallyOfFinitePresentation e p).1 h₃, fun t ↦ ?_⟩
    rw [← h₄ t, Scheme.Hom.finrank_comp_left_of_isIso]
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    refine ⟨inferInstance, inferInstance, inferInstance, fun t ↦ ?_⟩
    rw [Scheme.Hom.finrank_comp_left_of_isIso, h₄]

namespace Scheme.IdealSheafData

/-- Pushforward of ideal sheaves along a closed immersion commutes with arbitrary base change:
for a cartesian square whose right-hand edge `g` is a closed immersion, pushing forward along
`g` and then pulling back along `q` is pulling back along `p` and then pushing forward along
`g'`. -/
theorem map_comap_of_isPullback_of_isClosedImmersion {X' Y' X Y : Scheme.{u}}
    (B : Y.IdealSheafData) {g : Y ⟶ X} [IsClosedImmersion g] {q : X' ⟶ X} {g' : Y' ⟶ X'}
    {p : Y' ⟶ Y} (h : IsPullback p g' g q) : (B.map g).comap q = (B.comap p).map g' := by
  have H := ((IsPullback.of_hasPullback p B.subschemeι).paste_horiz h.flip)
  rw [map, map, ← ker_fst_of_isClosedImmersion, ← comapIso_hom_fst, Category.assoc,
    Scheme.Hom.ker_comp_of_isIso, ← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- If `I` contains the kernel of a closed immersion `j`, then `I` is the pushforward of its
pullback along `j`. -/
lemma map_comap_of_ker_le {U Y : Scheme.{u}} (j : U ⟶ Y) [IsClosedImmersion j]
    (I : Y.IdealSheafData) (hI : j.ker ≤ I) : (I.comap j).map j = I := by
  have hI' : j.ker ≤ I.subschemeι.ker := by rwa [ker_subschemeι]
  have hpb : IsPullback (IsClosedImmersion.lift j I.subschemeι hI') (𝟙 _) j I.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have : IsIso (pullback.snd j I.subschemeι) := by
    rw [← hpb.isoPullback_inv_snd, Category.comp_id]
    infer_instance
  rw [map, ← comapIso_hom_fst, Category.assoc, Scheme.Hom.ker_comp_of_isIso, pullback.condition,
    Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]

end Scheme.IdealSheafData

variable {X Y S : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (g : Y ⟶ S)

/-- For a closed immersion `i : X ⟶ Y` over `S` and an `S`-scheme `T`, the closed immersion
`X ×[S] T ⟶ Y ×[S] T`. -/
noncomputable abbrev pullbackCompMap (T : Over S) :
    pullback (i ≫ g) T.hom ⟶ pullback g T.hom :=
  pullback.map _ _ _ _ i (𝟙 _) (𝟙 _) (by simp) (by simp)

omit [IsClosedImmersion i] in
/-- The closed immersion `X ×[S] T ⟶ Y ×[S] T` lies over `T`. -/
@[reassoc (attr := simp)]
lemma pullbackCompMap_snd (T : Over S) :
    pullbackCompMap i g T ≫ pullback.snd g T.hom = pullback.snd (i ≫ g) T.hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

omit [IsClosedImmersion i] in
/-- `X ×[S] T` is the preimage of `X` in `Y ×[S] T`. -/
lemma isPullback_pullbackCompMap (T : Over S) :
    IsPullback (pullbackCompMap i g T) (pullback.fst _ _) (pullback.fst g T.hom) i := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback g T.hom).flip
  rw [pullbackCompMap_snd]
  exact (IsPullback.of_hasPullback (i ≫ g) T.hom).flip

instance (T : Over S) : IsClosedImmersion (pullbackCompMap i g T) :=
  MorphismProperty.of_isPullback (isPullback_pullbackCompMap i g T).flip inferInstance

omit [IsClosedImmersion i] in
/-- The base change square of `X ×[S] T ⟶ Y ×[S] T` along `W ⟶ T`. -/
lemma isPullback_baseChangeMap_pullbackCompMap {T W : Over S} (b : W ⟶ T) :
    IsPullback (baseChangeMap (i ≫ g) b) (pullbackCompMap i g W) (pullbackCompMap i g T)
      (baseChangeMap g b) := by
  refine (IsPullback.of_bot ?_ ?_ (isPullback_pullbackCompMap i g T)).flip
  · simpa using isPullback_pullbackCompMap i g W
  · apply pullback.hom_ext <;> simp

/-- A point of `Hilb^d_{X/S}(T)` pushes forward to a point of `Hilb^d_{Y/S}(T)`. -/
lemma IsHilbertSubscheme.map_pullbackCompMap {d : ℕ} {T : Over S}
    {J : (pullback (i ≫ g) T.hom).IdealSheafData} (hJ : IsHilbertSubscheme (i ≫ g) d T J) :
    IsHilbertSubscheme g d T (J.map (pullbackCompMap i g T)) := by
  have key : (J.subschemeι ≫ pullbackCompMap i g T).toImage ≫
      (J.map (pullbackCompMap i g T)).subschemeι ≫ pullback.snd g T.hom =
      J.subschemeι ≫ pullback.snd _ T.hom := by
    rw [← Category.assoc]
    erw [Scheme.Hom.toImage_imageι]
    rw [Category.assoc, pullbackCompMap_snd]
  unfold IsHilbertSubscheme at hJ ⊢
  rw [← key] at hJ
  exact (isFinite_flat_finrank_iso_comp_iff _ _ d).1 hJ

/-- A point of `Hilb^d_{Y/S}(T)` lying in `X_T` restricts to a point of `Hilb^d_{X/S}(T)`. -/
lemma IsHilbertSubscheme.comap_pullbackCompMap {d : ℕ} {T : Over S}
    {I : (pullback g T.hom).IdealSheafData} (hI : IsHilbertSubscheme g d T I)
    (hIX : (pullbackCompMap i g T).ker ≤ I) :
    IsHilbertSubscheme (i ≫ g) d T (I.comap (pullbackCompMap i g T)) := by
  have hI' : (pullbackCompMap i g T).ker ≤ I.subschemeι.ker := by
    rwa [Scheme.IdealSheafData.ker_subschemeι]
  have hpb : IsPullback (IsClosedImmersion.lift _ I.subschemeι hI') (𝟙 _)
      (pullbackCompMap i g T) I.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have : IsIso (pullback.snd (pullbackCompMap i g T) I.subschemeι) := by
    rw [← hpb.isoPullback_inv_snd, Category.comp_id]
    infer_instance
  have key : ((I.comapIso _).hom ≫ pullback.snd (pullbackCompMap i g T) I.subschemeι) ≫
      I.subschemeι ≫ pullback.snd g _ =
      (I.comap (pullbackCompMap i g T)).subschemeι ≫ pullback.snd _ T.hom := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Category.assoc,
      ← pullback.condition_assoc, pullbackCompMap_snd]
  unfold IsHilbertSubscheme at hI ⊢
  rw [← key]
  exact (isFinite_flat_finrank_iso_comp_iff _ _ d).2 hI

/-- **`Hilb^d_{X/S}` is a subfunctor of `Hilb^d_{Y/S}`.** For a closed immersion `i : X ⟶ Y`,
pushing forward closed subschemes along the closed immersions `X ×[S] T ⟶ Y ×[S] T` is a
natural transformation `Hilb^d_{X/S} ⟶ Hilb^d_{Y/S}`. -/
noncomputable def hilbertPresheafCompι (d : ℕ) :
    hilbertPresheaf (i ≫ g) d ⟶ hilbertPresheaf g d where
  app T := TypeCat.ofHom fun J ↦ ⟨J.1.map (pullbackCompMap i g T.unop),
    J.2.map_pullbackCompMap i g⟩
  naturality W W' b := by
    ext J : 3
    exact Subtype.ext (Scheme.IdealSheafData.map_comap_of_isPullback_of_isClosedImmersion _
      (isPullback_baseChangeMap_pullbackCompMap i g b.unop)).symm

lemma hilbertPresheafCompι_app_coe (d : ℕ) {T : Over S}
    (J : (hilbertPresheaf (i ≫ g) d).obj (op T)) :
    ((hilbertPresheafCompι i g d).app (op T) J).1 = J.1.map (pullbackCompMap i g T) :=
  rfl

/-- The inclusion `Hilb^d_{X/S} ⟶ Hilb^d_{Y/S}` is injective. -/
lemma hilbertPresheafCompι_app_injective (d : ℕ) (T : Over S) :
    Function.Injective ((hilbertPresheafCompι i g d).app (op T)) := by
  intro J₁ J₂ hJ
  apply Subtype.ext
  rw [← Scheme.IdealSheafData.comap_map_of_isClosedImmersion (pullbackCompMap i g T) J₁.1,
    ← Scheme.IdealSheafData.comap_map_of_isClosedImmersion (pullbackCompMap i g T) J₂.1]
  exact congrArg (fun I ↦ Scheme.IdealSheafData.comap I _) (congrArg Subtype.val hJ)

/-- A point `Z` of `Hilb^d_{Y/S}(T)` comes from `Hilb^d_{X/S}(T)` if and only if `Z ⊆ X_T`. -/
lemma exists_hilbertPresheafCompι_app_eq_iff (d : ℕ) {T : Over S}
    (I : (hilbertPresheaf g d).obj (op T)) :
    (∃ J, (hilbertPresheafCompι i g d).app (op T) J = I) ↔
      (pullbackCompMap i g T).ker ≤ I.1 := by
  constructor
  · rintro ⟨J, rfl⟩
    rw [hilbertPresheafCompι_app_coe, ← Scheme.IdealSheafData.map_bot]
    exact Scheme.IdealSheafData.map_mono _ bot_le
  · intro hI
    exact ⟨⟨I.1.comap _, I.2.comap_pullbackCompMap i g hI⟩, Subtype.ext
      (Scheme.IdealSheafData.map_comap_of_ker_le _ _ hI)⟩

/-- The ideal sheaf of `X_{T'} ⊆ Y_{T'}` is the pullback of that of `X_T ⊆ Y_T`. -/
private lemma ker_pullbackCompMap_eq_comap {T T' : Over S} (a : T' ⟶ T) :
    (pullbackCompMap i g T').ker = (pullbackCompMap i g T).ker.comap (baseChangeMap g a) := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← (isPullback_baseChangeMap_pullbackCompMap i g a).flip.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

/-- The closed subscheme cut out by the pullback of an ideal sheaf is the pullback of the
closed subscheme. -/
private lemma isPullback_comap_subschemeι {X' Y' : Scheme.{u}}
    (I : Y'.IdealSheafData) (f : X' ⟶ Y') :
    IsPullback (I.comap f).subschemeι ((I.comapIso f).hom ≫ pullback.snd f I.subschemeι) f
      I.subschemeι :=
  IsPullback.of_iso_pullback ⟨by simp⟩ (I.comapIso f) (by simp) rfl

/-- On an affine scheme, an ideal sheaf vanishes iff its ideal of global sections does. -/
private lemma eq_bot_iff_ideal_top_eq_bot {X' : Scheme.{u}} [IsAffine X']
    (J : X'.IdealSheafData) : J = ⊥ ↔ J.ideal ⟨⊤, isAffineOpen_top X'⟩ = ⊥ := by
  refine ⟨fun h ↦ by simp [h], fun h ↦
    le_bot_iff.mp (Scheme.IdealSheafData.le_of_isAffine ?_)⟩
  simp [h]

/-- A finite, flat and finitely presented morphism of affine schemes makes the global sections
of the source a projective module over those of the target. -/
private lemma projective_appTop {X' Y' : Scheme.{u}} [IsAffine X'] [IsAffine Y'] (f : X' ⟶ Y')
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    letI := f.appTop.hom.toAlgebra; Module.Projective Γ(Y', ⊤) Γ(X', ⊤) := by
  algebraize [f.appTop.hom]
  have : Module.Finite Γ(Y', ⊤) Γ(X', ⊤) := f.finite_appTop
  have : Module.Flat Γ(Y', ⊤) Γ(X', ⊤) := f.flat_appTop
  have : Algebra.FinitePresentation Γ(Y', ⊤) Γ(X', ⊤) := f.finitePresentation_appTop
  have := Module.FinitePresentation.of_finite_of_finitePresentation Γ(Y', ⊤) Γ(X', ⊤)
  exact Module.Flat.projective_of_finitePresentation

/-- **The containment locus, affine case** (blueprint
`theorem-hilbert-schemes-points-smooth-curve--1`, Step 1). Let `T` be an affine `S`-scheme, `I` the
ideal of a point `Z` of `Hilb^d_{Y/S}(T)` and `J` the ideal of any closed subscheme `W ⊆ Y_T`. There
is a closed subscheme of `T`, given by its ideal sheaf `K`, such that for every affine `S`-scheme
`T'` over `T` the pullback `Z_{T'}` lies in `W_{T'}` if and only if `T' ⟶ T` factors through it.

Write `T = Spec A` and `Z = Spec B`, with `B` finite projective over `A`, and let `k ⊆ B` be the
image of `J`. Then `K` is generated by the values on `k` of the `A`-linear forms on `B`
(`Submodule.dualContent`). -/
theorem exists_le_ker_iff_comap_le_of_isAffine {d : ℕ} {T : Over S} [IsAffine T.left]
    {I : (pullback g T.hom).IdealSheafData} (hI : IsHilbertSubscheme g d T I)
    (J : (pullback g T.hom).IdealSheafData) :
    ∃ K : T.left.IdealSheafData, ∀ (W : Over S) [IsAffine W.left] (a : W ⟶ T),
      K ≤ a.left.ker ↔ J.comap (baseChangeMap g a) ≤ I.comap (baseChangeMap g a) := by
  have : IsFinite (I.subschemeι ≫ pullback.snd g T.hom) := hI.1
  have : Flat (I.subschemeι ≫ pullback.snd g T.hom) := hI.2.1
  have : LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd g T.hom) := hI.2.2.1
  have : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ pullback.snd g T.hom)
  let k := (J.comap I.subschemeι).ideal ⟨⊤, isAffineOpen_top _⟩
  let := (I.subschemeι ≫ pullback.snd g T.hom).appTop.hom.toAlgebra
  refine ⟨.ofIdealTop (k.restrictScalars Γ(T.left, ⊤)).dualContent, fun W _ a ↦ ?_⟩
  have hJ := hI.comap a
  have : IsFinite ((I.comap (baseChangeMap g a)).subschemeι ≫ pullback.snd g W.hom) := hJ.1
  have : Flat ((I.comap (baseChangeMap g a)).subschemeι ≫ pullback.snd g W.hom) := hJ.2.1
  have : LocallyOfFinitePresentation
      ((I.comap (baseChangeMap g a)).subschemeι ≫ pullback.snd g W.hom) := hJ.2.2.1
  have : IsAffine (I.comap (baseChangeMap g a)).subscheme :=
    isAffine_of_isAffineHom ((I.comap (baseChangeMap g a)).subschemeι ≫ pullback.snd g W.hom)
  have hpb := (isPullback_comap_subschemeι I (baseChangeMap g a)).flip.paste_vert
    (isPullback_baseChangeMap g a)
  have key : J.comap (baseChangeMap g a) ≤ I.comap (baseChangeMap g a) ↔
      (J.comap I.subschemeι).comap
        ((I.comapIso (baseChangeMap g a)).hom ≫ pullback.snd _ I.subschemeι) = ⊥ := by
    rw [← Scheme.IdealSheafData.comap_comp,
      ← (isPullback_comap_subschemeι I (baseChangeMap g a)).w,
      Scheme.IdealSheafData.comap_comp]
    refine ⟨fun h ↦ le_bot_iff.mp ((Scheme.IdealSheafData.comap_mono _ h).trans_eq
      (Scheme.IdealSheafData.comap_subschemeι _)), fun h ↦ ?_⟩
    exact (Scheme.IdealSheafData.le_ker_of_comap_eq_bot _ h).trans_eq
      (Scheme.IdealSheafData.ker_subschemeι _)
  refine Iff.symm (key.trans ?_)
  rw [Scheme.ker_of_isAffine, ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply,
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, map_le_map_iff,
    ← Ideal.map_eq_bot_iff_le_ker,
    ← CommRingCat.map_eq_bot_iff_of_isPushout (isPushout_appTop_of_isPullback hpb)
      (projective_appTop _),
    eq_bot_iff_ideal_top_eq_bot,
    Scheme.IdealSheafData.ideal_top_comap_of_isAffine]

/-- **The closed-immersion claim** (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`, Step
1). For a closed immersion `i : X ⟶ Y`, an affine `S`-scheme `T` and `Z ∈ Hilb^d_{Y/S}(T)`, there is
a closed subscheme `T_X ⊆ T`, given by its ideal sheaf `K`, such that for every affine `W` over `T`
the pullback `Z_W` lies in `X_W` if and only if `W ⟶ T` factors through `T_X`. -/
theorem exists_le_ker_iff_mem_range_hilbertPresheafCompι (d : ℕ) (T : Over S)
    [IsAffine T.left] (z : (hilbertPresheaf g d).obj (op T)) :
    ∃ K : T.left.IdealSheafData, ∀ (W : Over S) [IsAffine W.left] (a : W ⟶ T),
      (∃ x, (hilbertPresheafCompι i g d).app (op W) x = (hilbertPresheaf g d).map a.op z) ↔
        K ≤ a.left.ker := by
  obtain ⟨K, hK⟩ := exists_le_ker_iff_comap_le_of_isAffine g z.2 (pullbackCompMap i g T).ker
  refine ⟨K, fun W _ a ↦ ?_⟩
  rw [exists_hilbertPresheafCompι_app_eq_iff, hK W a, ker_pullbackCompMap_eq_comap i g a]
  rfl

/-- **The closed-immersion claim, representability** (blueprint
`theorem-hilbert-schemes-points-smooth-curve--1`, Step 1). For a closed immersion `i : X ⟶ Y` and
`g : Y ⟶ S`, the functor `Hilb^d_{X/S}` is a closed subfunctor of `Hilb^d_{Y/S}`; in particular, if
`Hilb^d_{Y/S}` is representable, so is `Hilb^d_{X/S}`, by a closed subscheme. -/
theorem isRepresentable_hilbertPresheaf_of_isClosedImmersion (d : ℕ)
    (hg : (hilbertPresheaf g d).IsRepresentable) :
    (hilbertPresheaf (i ≫ g) d).IsRepresentable := by
  let P := hilbertPresheaf (i ≫ g) d
  let Φ := hilbertPresheafCompι i g d
  obtain ⟨H, ⟨e⟩⟩ := hg.has_representation
  -- the affine opens `V` of `H`, as `S`-schemes
  let TV (V : H.left.affineOpens) : Over S := Over.mk (V.1.ι ≫ H.hom)
  let jV (V : H.left.affineOpens) : TV V ⟶ H := Over.homMk V.1.ι
  have hclaim (V : H.left.affineOpens) :=
    haveI : IsAffine (TV V).left := V.2
    exists_le_ker_iff_mem_range_hilbertPresheafCompι i g d (TV V) (e.homEquiv (jV V))
  choose K hK using hclaim
  -- the closed subschemes `K_V ⊆ V` over which the universal element comes from `X`
  let X' (V : H.left.affineOpens) : Over S := Over.mk ((K V).subschemeι ≫ V.1.ι ≫ H.hom)
  let cV (V : H.left.affineOpens) : X' V ⟶ TV V := Over.homMk (K V).subschemeι
  let π (V : H.left.affineOpens) : X' V ⟶ H := cV V ≫ jV V
  have hξ (V : H.left.affineOpens) : ∃ x, Φ.app (op (X' V)) x = e.homEquiv (π V) := by
    have : IsAffine (TV V).left := V.2
    have : IsAffine (X' V).left := isAffine_of_isAffineHom (K V).subschemeι
    rw [e.homEquiv_comp]
    refine (hK V (X' V) (cV V)).2 ?_
    simp [cV, Scheme.IdealSheafData.ker_subschemeι]
  choose ξ hξ using hξ
  have hΦξ (V : H.left.affineOpens) {T : Over S} (a : T ⟶ X' V) :
      Φ.app (op T) (P.map a.op (ξ V)) = e.homEquiv (a ≫ π V) := by
    rw [e.homEquiv_comp, ← hξ, NatTrans.naturality_apply]
  -- the classifying map of the image of `x` in `Hilb^d_{Y/S}`
  let φ {T : Over S} (x : P.obj (op T)) : T ⟶ H := e.homEquiv.symm (Φ.app (op T) x)
  have hφ {T W : Over S} (x : P.obj (op T)) (a : W ⟶ T) :
      Φ.app (op W) (P.map a.op x) = e.homEquiv (a ≫ φ x) := by
    rw [e.homEquiv_comp, Equiv.apply_symm_apply, NatTrans.naturality_apply]
  have hfac (V : H.left.affineOpens) {T W : Over S} [IsAffine W.left] (x : P.obj (op T))
      (a : W ⟶ T) (h : Set.range a.left ⊆ (φ x).left ⁻¹' V.1) :
      ∃ b : W ⟶ X' V, P.map a.op x = P.map b.op (ξ V) := by
    have h' : Set.range (a.left ≫ (φ x).left) ⊆ Set.range V.1.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      exact h ⟨w, rfl⟩
    let c := IsOpenImmersion.lift V.1.ι _ h'
    have hc : c ≫ V.1.ι = a.left ≫ (φ x).left := IsOpenImmersion.lift_fac _ _ _
    let c' : W ⟶ TV V := Over.homMk c (by
      simp only [TV, Over.mk_hom]
      rw [← Category.assoc, hc, Category.assoc, Over.w, Over.w])
    have hc' : c' ≫ jV V = a ≫ φ x := by
      ext
      exact hc
    have hKc : K V ≤ c.ker := by
      have : IsAffine (TV V).left := V.2
      refine (hK V W c').1 ⟨P.map a.op x, ?_⟩
      rw [hφ, ← hc', e.homEquiv_comp]
    let b' := IsClosedImmersion.lift (K V).subschemeι c
      (by rwa [Scheme.IdealSheafData.ker_subschemeι])
    let b : W ⟶ X' V := Over.homMk b' (by
      simp only [X', Over.mk_hom, b', IsClosedImmersion.lift_fac_assoc]
      exact Over.w c')
    refine ⟨b, hilbertPresheafCompι_app_injective i g d W ?_⟩
    have hb : b ≫ π V = a ≫ φ x := by
      rw [← hc']
      ext
      simp [b, b', π, cV, jV, c']
    rw [hΦξ, hφ, hb]
  have hinj (V : H.left.affineOpens) {T : Over S} [IsAffine T.left] (a b : T ⟶ X' V)
      (hab : P.map a.op (ξ V) = P.map b.op (ξ V)) : a = b := by
    have h : a ≫ π V = b ≫ π V := e.homEquiv.injective (by rw [← hΦξ, ← hΦξ, hab])
    have : Mono (π V).left := by
      simp only [π, cV, jV, Over.comp_left, Over.homMk_left]
      infer_instance
    ext
    rw [← cancel_mono (π V).left, ← Over.comp_left, ← Over.comp_left, h]
  have hopen (V : H.left.affineOpens) (T : Over S) [IsAffine T.left] (x : P.obj (op T)) :
      ∃ U : T.left.Opens, ∀ (W : Over S) [IsAffine W.left] (a : W ⟶ T),
        (∃ b : W ⟶ X' V, P.map a.op x = P.map b.op (ξ V)) ↔ Set.range a.left ⊆ U := by
    refine ⟨(φ x).left ⁻¹ᵁ V.1, fun W _ a ↦ ⟨?_, hfac V x a⟩⟩
    rintro ⟨b, hb⟩ _ ⟨w, rfl⟩
    have h : b ≫ π V = a ≫ φ x := e.homEquiv.injective (by rw [← hΦξ, ← hφ, hb])
    have hw : (a ≫ φ x).left w ∈ V.1 := by
      rw [← h]
      simp only [π, cV, jV, Over.comp_left, Over.homMk_left, Scheme.Hom.comp_apply]
      exact ((K V).subschemeι (b.left w)).2
    simpa using hw
  have hcov (T : Over S) [IsAffine T.left] (x : P.obj (op T)) (t : T.left) :
      ∃ (V : H.left.affineOpens) (W : Over S) (a : W ⟶ T) (b : W ⟶ X' V),
        t ∈ Set.range a.left ∧ P.map a.op x = P.map b.op (ξ V) := by
    obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ := H.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((φ x).left t)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, htU, hUV⟩ := T.left.isBasis_affineOpens.exists_subset_of_mem_open
      (a := t) (ou := ((φ x).left ⁻¹ᵁ V).2) htV
    let W : Over S := Over.mk (Scheme.Opens.ι U ≫ T.hom)
    let a : W ⟶ T := Over.homMk (Scheme.Opens.ι U) rfl
    have : IsAffine W.left := hU
    obtain ⟨b, hb⟩ := hfac ⟨V, hV⟩ x a (by
      rintro _ ⟨u, rfl⟩
      exact hUV u.2)
    exact ⟨⟨V, hV⟩, W, a, b, ⟨⟨t, htU⟩, rfl⟩, hb⟩
  exact Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over_of_isAffine P
    (isSheaf_zariskiTopology_hilbertPresheaf _ d) X' ξ hinj hopen hcov

/-- **The containment locus is closed** (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`,
Step 1, the closed-immersion claim). Let `I` be a point of `Hilb^d_{Y/S}(T)`, i.e. the ideal of a
closed subscheme `Z ⊆ Y_T` finite locally free over `T`, and let `J` be the ideal of any closed
subscheme `W ⊆ Y_T`. There is a closed subscheme of `T`, with ideal `K`, such that an
`S`-morphism `φ : T' ⟶ T` factors through it if and only if `Z_{T'} ⊆ W_{T'}`.

Over the affine opens of `T` this is `exists_le_ker_iff_comap_le_of_isAffine`. These local
ideal sheaves are determined by this property, hence glue
(`Scheme.IdealSheafData.exists_comap_ι_eq`), and both sides of the equivalence are local
on `T'`. -/
theorem exists_idealSheafData_le_ker_iff_comap_le {d : ℕ} {T : Over S}
    {I : (pullback g T.hom).IdealSheafData} (hI : IsHilbertSubscheme g d T I)
    (J : (pullback g T.hom).IdealSheafData) :
    ∃ K : T.left.IdealSheafData, ∀ (T' : Over S) (φ : T' ⟶ T),
      K ≤ φ.left.ker ↔ J.comap (baseChangeMap g φ) ≤ I.comap (baseChangeMap g φ) := by
  let P {T' : Over S} (φ : T' ⟶ T) : Prop :=
    J.comap (baseChangeMap g φ) ≤ I.comap (baseChangeMap g φ)
  have hP {T' T'' : Over S} (ψ : T'' ⟶ T') (φ : T' ⟶ T) (h : P φ) : P (ψ ≫ φ) := by
    simp only [P, baseChangeMap_comp, Scheme.IdealSheafData.comap_comp]
    exact Scheme.IdealSheafData.comap_mono _ h
  have hPiso {T₁ T₂ : Over S} (e : T₁ ≅ T₂) (φ₁ : T₁ ⟶ T) (φ₂ : T₂ ⟶ T)
      (h : e.hom ≫ φ₂ = φ₁) : P φ₁ ↔ P φ₂ := by
    refine ⟨fun h₁ ↦ ?_, fun h₂ ↦ h ▸ hP _ _ h₂⟩
    have := hP e.inv _ h₁
    rwa [← h, e.inv_hom_id_assoc] at this
  -- the affine opens of `T`, as `S`-schemes, and the containment loci over them
  let TU (U : T.left.affineOpens) : Over S := Over.mk (U.1.ι ≫ T.hom)
  let ιU (U : T.left.affineOpens) : TU U ⟶ T := Over.homMk U.1.ι
  have hKU (U : T.left.affineOpens) : ∃ K : U.1.toScheme.IdealSheafData,
      ∀ (W : Over S) [IsAffine W.left] (a : W ⟶ TU U), K ≤ a.left.ker ↔ P (a ≫ ιU U) := by
    have : IsAffine (TU U).left := U.2
    obtain ⟨K, hK⟩ := exists_le_ker_iff_comap_le_of_isAffine g (hI.comap (ιU U))
      (J.comap (baseChangeMap g (ιU U)))
    refine ⟨K, fun W _ a ↦ (hK W a).trans ?_⟩
    simp only [P, baseChangeMap_comp, Scheme.IdealSheafData.comap_comp]
  choose K hK using hKU
  -- the local containment loci agree on basic opens, hence glue
  have hcompat (U : T.left.affineOpens) (f : Γ(T.left, U)) :
      (K U).comap (T.left.homOfLE (T.left.basicOpen_le f)) = K (T.left.affineBasicOpen f) := by
    have : IsAffine (T.left.affineBasicOpen f).1.toScheme := (T.left.affineBasicOpen f).2
    have : IsAffine (T.left.basicOpen f).toScheme := (T.left.affineBasicOpen f).2
    refine Scheme.IdealSheafData.eq_of_forall_le_ker_iff fun W _ a ↦ ?_
    rw [Scheme.IdealSheafData.comap_le_ker_iff]
    refine (@hK U (Over.mk ((a ≫ T.left.homOfLE (T.left.basicOpen_le f)) ≫ U.1.ι ≫ T.hom))
      (by exact ‹IsAffine W›) (Over.homMk (a ≫ T.left.homOfLE (T.left.basicOpen_le f)))).trans
      (Iff.trans ?_ (@hK (T.left.affineBasicOpen f)
        (Over.mk (a ≫ (T.left.affineBasicOpen f).1.ι ≫ T.hom))
        (by exact ‹IsAffine W›) (Over.homMk a)).symm)
    refine hPiso (T₁ := Over.mk ((a ≫ T.left.homOfLE (T.left.basicOpen_le f)) ≫ U.1.ι ≫ T.hom))
      (T₂ := Over.mk (a ≫ (T.left.affineBasicOpen f).1.ι ≫ T.hom))
      (Over.isoMk (Iso.refl W) (by simp [Scheme.homOfLE_ι_assoc]; rfl)) _ _ ?_
    ext
    simp [TU, ιU, Scheme.homOfLE_ι]
    rfl
  obtain ⟨K₀, hK₀⟩ := Scheme.IdealSheafData.exists_comap_ι_eq K hcompat
  -- the containment locus over an affine open of `T'` mapping to an affine open of `T`
  have hloc (T' : Over S) (φ : T' ⟶ T) (U : T.left.affineOpens) (V : T'.left.affineOpens)
      (hUV : V.1 ≤ φ.left ⁻¹ᵁ U.1) :
      K₀ ≤ (V.1.ι ≫ φ.left).ker ↔
        P ((Over.homMk V.1.ι : Over.mk (V.1.ι ≫ T'.hom) ⟶ T') ≫ φ) := by
    rw [← φ.left.resLE_comp_ι hUV, ← Scheme.IdealSheafData.comap_le_ker_iff, hK₀]
    refine (@hK U (Over.mk (φ.left.resLE U.1 V.1 hUV ≫ U.1.ι ≫ T.hom)) V.2
      (Over.homMk (φ.left.resLE U.1 V.1 hUV))).trans ?_
    refine hPiso (T₁ := Over.mk (φ.left.resLE U.1 V.1 hUV ≫ U.1.ι ≫ T.hom))
      (T₂ := Over.mk (V.1.ι ≫ T'.hom))
      (Over.isoMk (Iso.refl _) (by simp [Scheme.Hom.resLE_comp_ι_assoc])) _ _ ?_
    ext
    simp [TU, ιU]
  refine ⟨K₀, fun T' φ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · -- `Z_{T'} ⊆ W_{T'}` may be checked over the affine opens of `T'`
    let ι' := {p : T.left.affineOpens × T'.left.affineOpens // p.2.1 ≤ φ.left ⁻¹ᵁ p.1.1}
    let ιV (p : ι') :
        Over.mk (p.1.2.1.ι ≫ T'.hom) ⟶ T' := Over.homMk p.1.2.1.ι
    have hpb (p : ι') := isPullback_baseChangeMap g (ιV p)
    have (p : ι') : IsOpenImmersion (baseChangeMap g (ιV p)) :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hpb p).flip
        (show IsOpenImmersion p.1.2.1.ι from inferInstance)
    refine Scheme.IdealSheafData.le_of_forall_comap_le (fun p ↦ baseChangeMap g (ιV p)) ?_
      fun p ↦ ?_
    · rw [eq_top_iff]
      intro z _
      obtain ⟨_, ⟨U, hU, rfl⟩, htU, -⟩ := T.left.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (φ.left (pullback.snd g T'.hom z))) isOpen_univ
      obtain ⟨_, ⟨V, hV, rfl⟩, htV, hVU⟩ :=
        T'.left.isBasis_affineOpens.exists_subset_of_mem_open
          (a := pullback.snd g T'.hom z) htU (φ.left ⁻¹ᵁ U).2
      let p : ι' :=
        ⟨(⟨U, hU⟩, ⟨V, hV⟩), hVU⟩
      have hz : z ∈ Set.range (pullback.fst (pullback.snd g T'.hom) (ιV p).left) := by
        rw [Scheme.Pullback.range_fst]
        exact ⟨⟨_, htV⟩, rfl⟩
      obtain ⟨w, rfl⟩ := hz
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨p, (hpb p).isoPullback.inv w, ?_⟩
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
    · have := (hloc T' φ p.1.1 p.1.2 p.2).mp (h.trans (Scheme.Hom.le_ker_comp _ _))
      simpa only [P, baseChangeMap_comp, Scheme.IdealSheafData.comap_comp] using this
  · -- conversely, `K₀` is contained in the kernel of `φ` over the affine opens of `T'`
    refine Scheme.IdealSheafData.le_ker_of_comap_eq_bot _
      (Scheme.IdealSheafData.eq_of_comap_ι_eq φ.left fun U V hUV ↦ ?_)
    rw [Scheme.IdealSheafData.comap_bot, ← Scheme.IdealSheafData.comap_comp]
    refine le_bot_iff.mp (Scheme.IdealSheafData.le_map_iff_comap_le.mp ?_)
    rw [Scheme.IdealSheafData.map_bot]
    exact (hloc T' φ U V hUV).mpr (hP _ _ h)

end AlgebraicGeometry
