/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.Hilbert.AffineSpace
public import WeilConjectures.AlgebraicGeometry.Hilbert.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Hilbert.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability

/-!
# Representability of the Hilbert functor of points

We prove that for a separated morphism `f : X ⟶ S` such that every finite set of at most `d`
points of a fibre of `f` lies in an affine open of `X`, the Hilbert functor `Hilb^d_{X/S}` is
representable (Stacks, Proposition 0B9A).

The proof applies the gluing criterion
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over` to the
subfunctors `F_{V,U}` of `Hilb^d_{X/S}`, indexed by affine opens `V ⊆ S` and `U ⊆ f⁻¹ V`, of
those `Z ⊆ X_T` such that `T ⟶ S` factors through `V` and `Z ⊆ U_T`:

* `F_{V,U}` is identified with the Hilbert functor of the morphism of affine schemes
  `U ⟶ V` (`AlgebraicGeometry.hilbertPresheafResLEι`, which uses that `f` is separated), and
  this one is representable by the affine case
  `AlgebraicGeometry.isRepresentable_hilbertPresheaf_of_isAffine`, which embeds `U` into an
  affine space over `V`;
* the locus of `T` over which `Z ⊆ U_T` is open
  (`AlgebraicGeometry.Scheme.IdealSheafData.exists_opens_support_comap_subset`);
* the `F_{V,U}` cover `Hilb^d_{X/S}`: a fibre of `Z ⟶ T` has at most `d` points
  (`AlgebraicGeometry.Scheme.Hom.ncard_preimage_singleton_le_finrank`), so by assumption they
  lie in an affine open of `X`, which can be shrunk into `f⁻¹ V`
  (`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le_of_finite`).

## Main statements

- `AlgebraicGeometry.isRepresentable_hilbertPresheaf_of_isAffine`: the affine case, from the
  closed-immersion claim
  (`AlgebraicGeometry.isRepresentable_hilbertPresheaf_of_isClosedImmersion`) and the case of an
  affine space over an affine base
  (`AlgebraicGeometry.isRepresentable_hilbertPresheaf_affineSpace`).
- `AlgebraicGeometry.isRepresentable_hilbertPresheaf`: representability of `Hilb^d_{X/S}`
  (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The condition `Z ⊆ U_T` on a closed subscheme `Z ⊆ X_T` is stable under base change. -/
lemma Scheme.IdealSheafData.support_comap_baseChangeMap_subset (f : X ⟶ S) {T W : Over S}
    (a : W ⟶ T) {I : (pullback f T.hom).IdealSheafData} {U : Set X}
    (hI : (I.support : Set _) ⊆ pullback.fst f T.hom ⁻¹' U) :
    ((I.comap (baseChangeMap f a)).support : Set _) ⊆ pullback.fst f W.hom ⁻¹' U := by
  intro z hz
  rw [coe_support_comap] at hz
  have := hI hz
  simp only [Set.mem_preimage, ← Scheme.Hom.comp_apply, baseChangeMap,
    pullback.lift_fst] at this ⊢
  simpa using this

namespace Scheme.IdealSheafData

/-- **Openness of `F_U`** (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`, Step 5). Let
`I` be an ideal sheaf on `X_T` whose closed subscheme `Z` is universally closed over `T`, and let
`U ⊆ X` be open. Then there is an open `O ⊆ T`, the complement of the image in `T` of the points of
`Z` lying over `X \ U`, such that for every `a : W ⟶ T` the pullback `Z_W` lies over `U` if and only
if `a` factors through `O`. -/
theorem exists_opens_support_comap_subset (f : X ⟶ S) {T : Over S}
    (I : (pullback f T.hom).IdealSheafData)
    [UniversallyClosed (I.subschemeι ≫ pullback.snd f T.hom)] (U : X.Opens) :
    ∃ O : T.left.Opens,
      (∀ t, t ∈ O ↔ ∀ z ∈ I.support, pullback.snd f T.hom z = t → pullback.fst f T.hom z ∈ U) ∧
      ∀ (W : Over S) (a : W ⟶ T),
        ((I.comap (baseChangeMap f a)).support : Set _) ⊆ pullback.fst f W.hom ⁻¹' U ↔
          Set.range a.left ⊆ O := by
  let q := I.subschemeι ≫ pullback.snd f T.hom
  -- the image in `T` of the points of `Z` lying over `X \ U`
  let B : Set T.left := q '' ((I.subschemeι ≫ pullback.fst f T.hom) ⁻¹' (U : Set X)ᶜ)
  have hB : IsClosed B :=
    q.isClosedMap _ (U.isOpen.isClosed_compl.preimage (Scheme.Hom.continuous _))
  have hsupp {z} : z ∈ I.support ↔ z ∈ Set.range I.subschemeι := by
    rw [range_subschemeι]
    rfl
  refine ⟨⟨Bᶜ, hB.isOpen_compl⟩, fun t ↦ ?_, fun W a ↦ ?_⟩
  · change t ∉ B ↔ _
    constructor
    · intro ht z hz hzt
      by_contra hzU
      obtain ⟨y, rfl⟩ := hsupp.1 hz
      exact ht ⟨y, hzU, hzt⟩
    · rintro H ⟨y, hyU, rfl⟩
      exact hyU (H _ (hsupp.2 ⟨y, rfl⟩) rfl)
  · rw [coe_support_comap]
    change _ ↔ Set.range a.left ⊆ Bᶜ
    have hfst (z) : pullback.fst f T.hom (baseChangeMap f a z) = pullback.fst f W.hom z := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Category.comp_id]
    have hsnd (z) : pullback.snd f T.hom (baseChangeMap f a z) =
        a.left (pullback.snd f W.hom z) := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply]
    constructor
    · rintro H _ ⟨w, rfl⟩ ⟨y, hyU, hyt⟩
      obtain ⟨z, hz₁, hz₂⟩ := exists_preimage_of_isPullback (isPullback_baseChangeMap f a)
        (I.subschemeι y) w hyt
      have := H (show baseChangeMap f a z ∈ I.support from hz₁ ▸ hsupp.2 ⟨y, rfl⟩)
      rw [Set.mem_preimage, ← hfst, hz₁] at this
      exact hyU this
    · intro H z hz
      by_contra hzU
      obtain ⟨y, hy⟩ := hsupp.1 hz
      refine H ⟨pullback.snd f W.hom z, rfl⟩ ⟨y, ?_, ?_⟩
      · simpa [Scheme.Hom.comp_apply, hy, hfst] using hzU
      · simp [q, hy, hsnd]

end Scheme.IdealSheafData

section ResLE

variable (f : X ⟶ S) {V : S.Opens} {U : X.Opens} (h : U ≤ f ⁻¹ᵁ V)

/-- For an `S`-scheme `W` lying over the open `V ⊆ S` and an open `U ⊆ f ⁻¹ V`, the open
immersion `U ×[V] W ⟶ X ×[S] W`. -/
noncomputable abbrev pullbackResLEMap (W : Over V.toScheme) :
    pullback (f.resLE V U h) W.hom ⟶ pullback f ((Over.map V.ι).obj W).hom :=
  pullback.map _ _ _ _ U.ι (𝟙 _) V.ι (by simp [Scheme.Hom.resLE_comp_ι]) (by simp)

@[reassoc (attr := simp)]
lemma pullbackResLEMap_snd (W : Over V.toScheme) :
    pullbackResLEMap f h W ≫ pullback.snd f ((Over.map V.ι).obj W).hom =
      pullback.snd (f.resLE V U h) W.hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- `U ×[V] W` is the preimage of `U` in `X ×[S] W`. -/
lemma isPullback_pullbackResLEMap (W : Over V.toScheme) :
    IsPullback (pullback.fst _ _) (pullbackResLEMap f h W) U.ι
      (pullback.fst f ((Over.map V.ι).obj W).hom) := by
  have h₁ : IsPullback (pullback.snd _ _ ≫ 𝟙 _) (pullback.fst (f.resLE V U h) W.hom)
      (W.hom ≫ V.ι) (f.resLE V U h ≫ V.ι) :=
    (IsPullback.of_hasPullback _ _).flip.paste_horiz (IsPullback.of_horiz_isIso_mono ⟨by simp⟩)
  rw [Category.comp_id, Scheme.Hom.resLE_comp_ι,
    ← pullbackResLEMap_snd f h W] at h₁
  exact (IsPullback.of_right h₁ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback _ _).flip).flip

instance (W : Over V.toScheme) : IsOpenImmersion (pullbackResLEMap f h W) :=
  MorphismProperty.of_isPullback (isPullback_pullbackResLEMap f h W) inferInstance

/-- The image of `U ×[V] W ⟶ X ×[S] W` is the preimage of `U`. -/
lemma range_pullbackResLEMap (W : Over V.toScheme) :
    Set.range (pullbackResLEMap f h W) = pullback.fst f ((Over.map V.ι).obj W).hom ⁻¹' U := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← (isPullback_pullbackResLEMap f h W).w,
      Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι U]
    exact ⟨_, rfl⟩
  · intro hz
    rw [Set.mem_preimage, ← Scheme.Opens.range_ι U] at hz
    obtain ⟨u, hu⟩ := hz
    obtain ⟨y, -, hy⟩ :=
      Scheme.exists_preimage_of_isPullback (isPullback_pullbackResLEMap f h W) u z hu
    exact ⟨y, hy⟩

/-- A closed subscheme of `U ×[V] W` which is universally closed over `W` stays closed in
`X ×[S] W`, as `X ×[S] W ⟶ W` is separated. -/
lemma isClosedImmersion_subschemeι_comp_pullbackResLEMap [IsSeparated f] {W : Over V.toScheme}
    (J : (pullback (f.resLE V U h) W.hom).IdealSheafData)
    [UniversallyClosed (J.subschemeι ≫ pullback.snd _ W.hom)] :
    IsClosedImmersion (J.subschemeι ≫ pullbackResLEMap f h W) := by
  have : UniversallyClosed ((J.subschemeι ≫ pullbackResLEMap f h W) ≫
      pullback.snd f ((Over.map V.ι).obj W).hom) := by
    rw [Category.assoc, pullbackResLEMap_snd]
    infer_instance
  have := UniversallyClosed.of_comp_of_isSeparated (J.subschemeι ≫ pullbackResLEMap f h W)
    (pullback.snd f ((Over.map V.ι).obj W).hom)
  exact .of_isPreimmersion _ (Scheme.Hom.isClosedMap _).isClosed_range

/-- A point of `Hilb^d_{U/V}(W)` pushes forward to a point of `Hilb^d_{X/S}(W)`. -/
lemma IsHilbertSubscheme.map_pullbackResLEMap [IsSeparated f] {d : ℕ} {W : Over V.toScheme}
    {J : (pullback (f.resLE V U h) W.hom).IdealSheafData}
    (hJ : IsHilbertSubscheme (f.resLE V U h) d W J) :
    IsHilbertSubscheme f d ((Over.map V.ι).obj W) (J.map (pullbackResLEMap f h W)) := by
  have := hJ.1
  have := isClosedImmersion_subschemeι_comp_pullbackResLEMap f h J
  have key : (J.subschemeι ≫ pullbackResLEMap f h W).toImage ≫
      (J.map (pullbackResLEMap f h W)).subschemeι ≫ pullback.snd f _ =
      J.subschemeι ≫ pullback.snd _ W.hom := by
    rw [← Category.assoc]
    erw [Scheme.Hom.toImage_imageι]
    rw [Category.assoc]
    exact congrArg (J.subschemeι ≫ ·) (pullbackResLEMap_snd f h W)
  unfold IsHilbertSubscheme at hJ ⊢
  rw [← key] at hJ
  exact (isFinite_flat_finrank_iso_comp_iff _ _ d).1 hJ

/-- A point of `Hilb^d_{X/S}(W)` lying in `U_W` restricts to a point of `Hilb^d_{U/V}(W)`. -/
lemma IsHilbertSubscheme.comap_pullbackResLEMap {d : ℕ} {W : Over V.toScheme}
    {I : (pullback f ((Over.map V.ι).obj W).hom).IdealSheafData}
    (hI : IsHilbertSubscheme f d ((Over.map V.ι).obj W) I)
    (hIU : (I.support : Set _) ⊆ pullback.fst f ((Over.map V.ι).obj W).hom ⁻¹' U) :
    IsHilbertSubscheme (f.resLE V U h) d W (I.comap (pullbackResLEMap f h W)) := by
  have hI' : Set.range I.subschemeι ⊆ Set.range (pullbackResLEMap f h W) := by
    rwa [Scheme.IdealSheafData.range_subschemeι, range_pullbackResLEMap]
  have hpb : IsPullback (IsOpenImmersion.lift _ I.subschemeι hI') (𝟙 _)
      (pullbackResLEMap f h W) I.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have : IsIso (pullback.snd (pullbackResLEMap f h W) I.subschemeι) := by
    rw [← hpb.isoPullback_inv_snd, Category.comp_id]
    infer_instance
  have key : ((I.comapIso _).hom ≫ pullback.snd (pullbackResLEMap f h W) I.subschemeι) ≫
      I.subschemeι ≫ pullback.snd f _ =
      (I.comap (pullbackResLEMap f h W)).subschemeι ≫ pullback.snd _ W.hom := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Category.assoc,
      ← pullback.condition_assoc, pullbackResLEMap_snd]
  unfold IsHilbertSubscheme at hI ⊢
  rw [← key]
  exact (isFinite_flat_finrank_iso_comp_iff _ _ d).2 hI

/-- **`F_{V,U}` is the Hilbert functor of `U ⟶ V`** (blueprint
`theorem-hilbert-schemes-points-smooth-curve--1`, Step 3). For opens `V ⊆ S` and `U ⊆ f⁻¹ V`,
pushing forward closed subschemes along the open immersions `U ×[V] W ⟶ X ×[S] W` is a natural
transformation from `Hilb^d_{U/V}` to the restriction of `Hilb^d_{X/S}` to `V`-schemes. It is
injective with image the `Z ⊆ X_W` lying in `U_W`; this uses that a closed subscheme of `U_W` finite
over `W` is closed in `X_W`, as `f` is separated. -/
noncomputable def hilbertPresheafResLEι [IsSeparated f] (d : ℕ) :
    hilbertPresheaf (f.resLE V U h) d ⟶ (Over.map V.ι).op ⋙ hilbertPresheaf f d where
  app W := TypeCat.ofHom fun J ↦
    ⟨J.1.map (pullbackResLEMap f h W.unop), J.2.map_pullbackResLEMap f h⟩
  naturality W W' b := by
    ext J : 3
    apply Subtype.ext
    change (J.1.comap (baseChangeMap _ b.unop)).map (pullbackResLEMap f h W'.unop) =
      (J.1.map (pullbackResLEMap f h W.unop)).comap
        (baseChangeMap f ((Over.map V.ι).map b.unop))
    obtain ⟨J, hJ⟩ := J
    have := hJ.1
    have := isClosedImmersion_subschemeι_comp_pullbackResLEMap f h J
    have hsq : pullbackResLEMap f h W'.unop ≫ baseChangeMap f ((Over.map V.ι).map b.unop) =
        baseChangeMap (f.resLE V U h) b.unop ≫ pullbackResLEMap f h W.unop := by
      apply pullback.hom_ext <;> simp [pullbackResLEMap, baseChangeMap]
    rw [← Scheme.IdealSheafData.map_comap_of_subset_range (pullbackResLEMap f h W'.unop)
      ((J.map (pullbackResLEMap f h W.unop)).comap _)]
    · rw [← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp,
        Scheme.IdealSheafData.comap_map_of_isClosedImmersion]
    · rw [range_pullbackResLEMap]
      refine Scheme.IdealSheafData.support_comap_baseChangeMap_subset f _ ?_
      rw [← range_pullbackResLEMap f h]
      exact Scheme.IdealSheafData.support_map_subset_range _ _

lemma hilbertPresheafResLEι_app_coe [IsSeparated f] (d : ℕ) {W : Over V.toScheme}
    (J : (hilbertPresheaf (f.resLE V U h) d).obj (op W)) :
    ((hilbertPresheafResLEι f h d).app (op W) J).1 = J.1.map (pullbackResLEMap f h W) :=
  rfl

/-- The comparison `Hilb^d_{U/V} ⟶ Hilb^d_{X/S}` is injective. -/
lemma hilbertPresheafResLEι_app_injective [IsSeparated f] (d : ℕ) (W : Over V.toScheme) :
    Function.Injective ((hilbertPresheafResLEι f h d).app (op W)) := by
  intro J₁ J₂ hJ
  have := J₁.2.1
  have := J₂.2.1
  have := isClosedImmersion_subschemeι_comp_pullbackResLEMap f h J₁.1
  have := isClosedImmersion_subschemeι_comp_pullbackResLEMap f h J₂.1
  apply Subtype.ext
  rw [← Scheme.IdealSheafData.comap_map_of_isClosedImmersion (pullbackResLEMap f h W) J₁.1,
    ← Scheme.IdealSheafData.comap_map_of_isClosedImmersion (pullbackResLEMap f h W) J₂.1]
  exact congrArg (fun I ↦ Scheme.IdealSheafData.comap I _) (congrArg Subtype.val hJ)

/-- The image of `Hilb^d_{U/V} ⟶ Hilb^d_{X/S}` consists of subschemes lying in `U_W`. -/
lemma support_hilbertPresheafResLEι_app_subset [IsSeparated f] (d : ℕ) {W : Over V.toScheme}
    (J : (hilbertPresheaf (f.resLE V U h) d).obj (op W)) :
    ((J.1.map (pullbackResLEMap f h W)).support : Set _) ⊆
      pullback.fst f ((Over.map V.ι).obj W).hom ⁻¹' U := by
  have := J.2.1
  have := isClosedImmersion_subschemeι_comp_pullbackResLEMap f h J.1
  rw [← range_pullbackResLEMap f h W]
  exact Scheme.IdealSheafData.support_map_subset_range _ _

/-- Every point of `Hilb^d_{X/S}(W)` lying in `U_W` comes from `Hilb^d_{U/V}(W)`. -/
lemma exists_hilbertPresheafResLEι_app_eq [IsSeparated f] (d : ℕ) {W : Over V.toScheme}
    (I : (hilbertPresheaf f d).obj (op ((Over.map V.ι).obj W)))
    (hIU : (I.1.support : Set _) ⊆ pullback.fst f ((Over.map V.ι).obj W).hom ⁻¹' U) :
    ∃ J, (hilbertPresheafResLEι f h d).app (op W) J = I := by
  refine ⟨⟨I.1.comap (pullbackResLEMap f h W), I.2.comap_pullbackResLEMap f h hIU⟩,
    Subtype.ext ?_⟩
  rw [hilbertPresheafResLEι_app_coe]
  exact Scheme.IdealSheafData.map_comap_of_subset_range _ _
    (hIU.trans (range_pullbackResLEMap f h W).symm.subset)

end ResLE

/-- **The affine claim** (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`, Steps 1 and
4). For a morphism of affine schemes `f : X ⟶ S`, the Hilbert functor `Hilb^d_{X/S}` is
representable.

The functions on `X` define a closed immersion of `X` into an affine space over `S`, so this
follows from the case of affine spaces,
`AlgebraicGeometry.isRepresentable_hilbertPresheaf_affineSpace`, by the closed-immersion claim
`AlgebraicGeometry.isRepresentable_hilbertPresheaf_of_isClosedImmersion`. -/
theorem isRepresentable_hilbertPresheaf_of_isAffine (f : X ⟶ S) [IsAffine X] [IsAffine S]
    (d : ℕ) : (hilbertPresheaf f d).IsRepresentable := by
  let i : X ⟶ 𝔸(Γ(X, ⊤); S) := AffineSpace.homOfVector f id
  have : IsClosedImmersion i := .of_surjective_of_isAffine i fun a ↦
    ⟨AffineSpace.coord S a, AffineSpace.homOfVector_appTop_coord f id a⟩
  rw [← AffineSpace.homOfVector_over f id]
  exact isRepresentable_hilbertPresheaf_of_isClosedImmersion i _ d
    (isRepresentable_hilbertPresheaf_affineSpace _ S d)

/-- **Representability of `Hilb^d`, general case.** Assume that for every point `s` of `S` and
every finite set of at most `d` points of the fibre `X_s` there is an affine open of `X`
containing all of them; this holds for instance when `X ⟶ S` is quasi-projective, or when `X`
carries an ample invertible module. If moreover `X ⟶ S` is separated, then `Hilb^d_{X/S}` is
representable by a scheme.

Separatedness cannot be dropped: for the line with doubled origin over a field and `d = 1`,
every finite set of at most one point lies in an affine open, but `Hilb^1_{X/S}` is not
representable.

The proof glues the Hilbert schemes of the morphisms of affine schemes `U ⟶ V`, for affine opens
`V ⊆ S` and `U ⊆ f⁻¹ V`, using the gluing criterion
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over`.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`) -/
theorem isRepresentable_hilbertPresheaf (f : X ⟶ S) [IsSeparated f] (d : ℕ)
    (hf : ∀ (s : S) (t : Finset (f.fiber s)), t.card ≤ d →
      ∃ U : X.affineOpens, ∀ x ∈ t, (f.fiberι s).base x ∈ U.1) :
    (hilbertPresheaf f d).IsRepresentable := by
  let P := hilbertPresheaf f d
  -- the index set: affine opens `V ⊆ S` and `U ⊆ f⁻¹ V`
  let ι := {p : S.affineOpens × X.affineOpens // p.2.1 ≤ f ⁻¹ᵁ p.1.1}
  have hrep (i : ι) := (isRepresentable_hilbertPresheaf_of_isAffine
    (f.resLE i.1.1.1 i.1.2.1 i.2) d).has_representation
  choose Y hY using hrep
  let e (i : ι) := (hY i).some
  let Φ (i : ι) := hilbertPresheafResLEι f i.2 d
  let X' (i : ι) : Over S := (Over.map i.1.1.1.ι).obj (Y i)
  let ξ (i : ι) : P.obj (op (X' i)) := (Φ i).app (op (Y i)) ((e i).homEquiv (𝟙 _))
  have hξ (i : ι) {W' : Over i.1.1.1.toScheme} (b' : W' ⟶ Y i) :
      P.map ((Over.map i.1.1.1.ι).map b').op (ξ i) = (Φ i).app (op W') ((e i).homEquiv b') := by
    rw [← Category.comp_id b', (e i).homEquiv_comp]
    exact (NatTrans.naturality_apply (Φ i) b'.op _).symm
  -- an `S`-scheme lying over `V` comes from a `V`-scheme
  have hlift (i : ι) (W : Over S) (hW : Set.range W.hom ⊆ i.1.1.1) :
      ∃ (W' : Over i.1.1.1.toScheme) (ε : (Over.map i.1.1.1.ι).obj W' ≅ W),
        ∀ c : W ⟶ X' i, ∃ c' : W' ⟶ Y i, (Over.map i.1.1.1.ι).map c' = ε.hom ≫ c := by
    have hW' : Set.range W.hom ⊆ Set.range i.1.1.1.ι := by rwa [Scheme.Opens.range_ι]
    refine ⟨Over.mk (IsOpenImmersion.lift _ _ hW'),
      Over.isoMk (Iso.refl _) (by simp [IsOpenImmersion.lift_fac]), fun c ↦ ?_⟩
    have hc : c.left ≫ (Y i).hom = IsOpenImmersion.lift _ _ hW' := by
      rw [← cancel_mono i.1.1.1.ι]
      simpa [IsOpenImmersion.lift_fac, X'] using Over.w c
    exact ⟨Over.homMk c.left hc, by ext; simp⟩
  have hrange (i : ι) {W : Over S} (c : W ⟶ X' i) : Set.range W.hom ⊆ i.1.1.1 := by
    rw [← Over.w c]
    rintro _ ⟨w, rfl⟩
    simp [X']
  have hP {T W : Over S} (a : W ⟶ T) (x : P.obj (op T)) :
      (P.map a.op x).1 = x.1.comap (baseChangeMap f a) := rfl
  have hPiso {W W' : Over S} (ε : W' ≅ W) (x : P.obj (op W)) :
      P.map ε.inv.op (P.map ε.hom.op x) = x := by
    rw [← Functor.map_comp_apply, ← op_comp, ε.inv_hom_id, op_id, Functor.map_id_apply]
  have hPiso' {W W' : Over S} (ε : W' ≅ W) (x : P.obj (op W')) :
      P.map ε.hom.op (P.map ε.inv.op x) = x := by
    rw [← Functor.map_comp_apply, ← op_comp, ε.hom_inv_id, op_id, Functor.map_id_apply]
  have hinj (i : ι) {T : Over S} (a b : T ⟶ X' i) (hab : P.map a.op (ξ i) = P.map b.op (ξ i)) :
      a = b := by
    obtain ⟨W', ε, hc⟩ := hlift i T (hrange i a)
    obtain ⟨a', ha'⟩ := hc a
    obtain ⟨b', hb'⟩ := hc b
    have ha : a = ε.inv ≫ (Over.map i.1.1.1.ι).map a' := by simp [ha']
    have hb : b = ε.inv ≫ (Over.map i.1.1.1.ι).map b' := by simp [hb']
    rw [ha, hb, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
      hξ, hξ] at hab
    have hab' := congrArg (P.map ε.hom.op) hab
    rw [hPiso', hPiso'] at hab'
    have := hilbertPresheafResLEι_app_injective f i.2 d W' hab'
    rw [ha, hb, (e i).homEquiv.injective this]
  -- the open subscheme of `T` over which `x` comes from `X' i`
  have hopen' (i : ι) (T : Over S) (x : P.obj (op T)) : ∃ O : T.left.Opens,
      (∀ t, t ∈ O ↔ T.hom t ∈ i.1.1.1 ∧ ∀ z ∈ x.1.support, pullback.snd f T.hom z = t →
        pullback.fst f T.hom z ∈ i.1.2.1) ∧
      ∀ (W : Over S) (a : W ⟶ T),
        (∃ b : W ⟶ X' i, P.map a.op x = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ O := by
    have := x.2.1
    obtain ⟨O, hOmem, hO⟩ := x.1.exists_opens_support_comap_subset f i.1.2.1
    refine ⟨T.hom ⁻¹ᵁ i.1.1.1 ⊓ O, fun t ↦ ?_, fun W a ↦ ?_⟩
    · rw [← hOmem]
      rfl
    change _ ↔ Set.range a.left ⊆ T.hom ⁻¹' i.1.1.1 ∩ O
    rw [Set.subset_inter_iff, ← hO]
    constructor
    · rintro ⟨b, hb⟩
      have hW := hrange i b
      refine ⟨?_, ?_⟩
      · rintro _ ⟨w, rfl⟩
        refine hW ⟨w, ?_⟩
        rw [← Over.w a]
        rfl
      · obtain ⟨W', ε, hc⟩ := hlift i W hW
        obtain ⟨b', hb'⟩ := hc b
        rw [← hP, hb, show b = ε.inv ≫ (Over.map i.1.1.1.ι).map b' by simp [hb'], op_comp,
          Functor.map_comp_apply, hξ, hP]
        exact Scheme.IdealSheafData.support_comap_baseChangeMap_subset f _
          (support_hilbertPresheafResLEι_app_subset f i.2 d _)
    · rintro ⟨hV, hU⟩
      have hW : Set.range W.hom ⊆ i.1.1.1 := by
        rintro _ ⟨w, rfl⟩
        rw [← Over.w a]
        exact hV ⟨w, rfl⟩
      obtain ⟨W', ε, hc⟩ := hlift i W hW
      let y := P.map ε.hom.op (P.map a.op x)
      have hy : (y.1.support : Set _) ⊆ pullback.fst f ((Over.map i.1.1.1.ι).obj W').hom ⁻¹'
          i.1.2.1 :=
        Scheme.IdealSheafData.support_comap_baseChangeMap_subset f _ hU
      obtain ⟨J, hJ⟩ := exists_hilbertPresheafResLEι_app_eq f i.2 d y hy
      refine ⟨ε.inv ≫ (Over.map i.1.1.1.ι).map ((e i).homEquiv.symm J), ?_⟩
      rw [op_comp, Functor.map_comp_apply, hξ, Equiv.apply_symm_apply, hJ, hPiso]
  have hopen (i : ι) (T : Over S) (x : P.obj (op T)) : ∃ O : T.left.Opens,
      ∀ (W : Over S) (a : W ⟶ T),
        (∃ b : W ⟶ X' i, P.map a.op x = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ O := by
    obtain ⟨O, -, hO⟩ := hopen' i T x
    exact ⟨O, hO⟩
  have hcov (T : Over S) (x : P.obj (op T)) (t : T.left) :
      ∃ (i : ι) (W : Over S) (a : W ⟶ T) (b : W ⟶ X' i),
        t ∈ Set.range a.left ∧ P.map a.op x = P.map b.op (ξ i) := by
    obtain ⟨-, -, -, hdeg⟩ := x.2
    have := x.2.1
    have := x.2.2.1
    have := x.2.2.2.1
    let p := x.1.subschemeι ≫ pullback.snd f T.hom
    let s := T.hom t
    -- an affine open neighbourhood `V` of `s`
    obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
    let V : S.affineOpens := ⟨V, hV⟩
    -- the points of `X` under the fibre of `Z ⟶ T` over `t`
    let F : Set X := (fun y ↦ pullback.fst f T.hom (x.1.subschemeι y)) '' (p ⁻¹' {t})
    have hFfin : F.Finite := (p.finite_preimage_singleton t).image _
    have hFcard : F.ncard ≤ d :=
      (Set.ncard_image_le (p.finite_preimage_singleton t)).trans
        ((p.ncard_preimage_singleton_le_finrank t).trans (hdeg t).le)
    have hFs : F ⊆ f ⁻¹' {s} := by
      rintro _ ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
      have : f (pullback.fst f T.hom (x.1.subschemeι y)) = T.hom (p y) := by
        simp only [p, ← Scheme.Hom.comp_apply, Category.assoc, pullback.condition]
      rw [this, hy]
    have hinjι : Function.Injective (f.fiberι s) := fun a b hab ↦
      (f.fiberHomeo s).injective (Subtype.ext (by simpa using hab))
    have hGfin : (f.fiberι s ⁻¹' F).Finite := hFfin.preimage hinjι.injOn
    obtain ⟨U', hU'⟩ := hf s hGfin.toFinset (by
      rw [← Set.ncard_eq_toFinset_card _ hGfin]
      exact (Set.ncard_preimage_of_injective_subset_range hinjι
        (hFs.trans (f.range_fiberι s).symm.subset)).le.trans hFcard)
    have hFU' : F ⊆ U'.1 := by
      intro x' hx'
      obtain ⟨y, rfl⟩ := (f.range_fiberι s).symm.subset (hFs hx')
      exact hU' y (by simpa using hx')
    -- shrink `U'` to an affine open `U ⊆ f⁻¹ V` still containing `F`
    obtain ⟨r, hFr, hr⟩ := U'.2.exists_basicOpen_le_of_finite (O := U'.1 ⊓ f ⁻¹ᵁ V.1)
      inf_le_left hFfin (fun x' hx' ↦ ⟨hFU' hx', by
        change f x' ∈ (V.1 : Set S)
        rw [(hFs hx' : f x' = s)]
        exact hsV⟩)
    let i : ι := ⟨(V, ⟨X.basicOpen r, U'.2.basicOpen r⟩), hr.trans inf_le_right⟩
    obtain ⟨O, hOmem, hO⟩ := hopen' i T x
    have htO : t ∈ O := by
      refine (hOmem t).2 ⟨hsV, fun z hz hzt ↦ hFr ?_⟩
      have hz' : z ∈ Set.range x.1.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact hz
      obtain ⟨y, rfl⟩ := hz'
      exact ⟨y, by simpa [p] using hzt, rfl⟩
    let a : Over.mk (O.ι ≫ T.hom) ⟶ T := Over.homMk O.ι rfl
    obtain ⟨b, hb⟩ := (hO _ a).2 (by simp [a])
    exact ⟨i, _, a, b, by simpa [a] using htO, hb⟩
  exact Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over P
    (isSheaf_zariskiTopology_hilbertPresheaf f d) X' ξ hinj hopen hcov

end AlgebraicGeometry
