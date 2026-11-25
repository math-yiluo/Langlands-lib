/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependenceField
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomFrames

/-!
# The fundamental class of a closed immersion with Thom frames

Let `i : Z ⟶ X` be a closed immersion which has Thom frames of codimension `c`
(`AlgebraicGeometry.Etale.HasThomFrames`) and regular Zariski frames
(`AlgebraicGeometry.Etale.HasRegularZariskiFrames`), with `X` locally of finite type over a
field. This file reruns the construction of the fundamental class `[Z ⊂ X]` of blueprint
`lemma-class-of-point--1` (`WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion`) under
these hypotheses, which hold étale-locally for the zero section of affine space, e.g. for the
diagonal of a smooth morphism, and without using smooth purity: clause (a) is
`AlgebraicGeometry.Etale.HasThomFrames.isZero_homology_rightDerivedLowerShriek`, and frame
independence is the version over a field
`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec_of_field`.

The frame classes glue to a unique class `[Z ⊂ X] ∈ H^{2c}_Z(X, Λ(c))` restricting to the frame
class on every frame, and its adjoint `cl_i : Λ_Z ⟶ Ri^! (Λ_X(c)[2c])` is an isomorphism, as it
is so on every Thom frame.

## Main definitions

- `AlgebraicGeometry.Etale.thomFundamentalClass`: the fundamental class `[Z ⊂ X]`.
- `AlgebraicGeometry.Etale.thomFundamentalClassMap`: `cl_i : Λ_Z ⟶ Ri^! (Λ_X(c)[2c])`.

## Main statements

- `AlgebraicGeometry.Etale.HasThomFrames.existsUnique_fundamentalClass`: existence and
  uniqueness of the fundamental class.
- `AlgebraicGeometry.Etale.isIso_thomFundamentalClassMap`: `cl_i` is an isomorphism.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_tateObject_of_hasThomFrames`:
  `Ri^! (Λ_X(c)[2c]) ≅ Λ_Z`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Z : Scheme.{u}} [HasInvertibleExponent Λ X] {c : ℕ}
  {i : Z ⟶ X} [IsClosedImmersion i]

attribute [local instance] HasInvertibleExponent.opens

variable {Λ}

omit [HasKummerClass.IsNormalized Λ] in
/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

*Uniqueness of the fundamental class, for closed immersions with Thom frames.* Two classes in
`H^{2c}_Z(X, Λ(c))` are equal if every point of `Z` lies in a Zariski frame on which their
restrictions agree. The classes are sections of a sheaf
(`AlgebraicGeometry.Etale.HasThomFrames.exists_iso_singleFunctor_rightDerivedLowerShriek`),
so they are determined by their pullbacks to the geometric points of `X`. A geometric point
outside `Z` sees nothing; a geometric point of `Z` factors through a Zariski frame, and the
restriction of supports along an open immersion is invertible
(`AlgebraicGeometry.Etale.isIso_supportedRestriction_of_isOpenImmersion`). -/
theorem HasThomFrames.eq_of_forall_exists_frameRestriction_eq (hT : HasThomFrames Λ c i)
    {γ γ' : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))}
    (h : ∀ z : Z, ∃ F : i.EtaleFrame c, IsOpenImmersion F.e ∧ z ∈ Set.range F.toZ ∧
      frameRestriction Λ F γ = frameRestriction Λ F γ') :
    γ = γ' := by
  obtain ⟨G, ⟨eM⟩⟩ := hT.exists_iso_singleFunctor_rightDerivedLowerShriek
  refine hom_ext_of_leftDerivedUpperStar_map_eq (constantComplexIsoSingleFunctor Λ X) eM
    fun Ω _ _ x ↦ ?_
  have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  by_cases hx : Set.range x.base ⊆ Set.range i.openComplement.ι.base
  · -- `x` misses `Z`, where the classes live
    refine (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint
      (ModuleCat.{u + 1} Λ) i i.openComplement.ι ?_ x hx _).eq_of_tgt _ _
    rw [i.range_eq_compl_range_openComplement_ι]
    exact disjoint_compl_left
  · -- `x` is a point of `Z`, which lies in a Zariski frame
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := Set.not_subset.mp hx
    rw [← Set.mem_compl_iff, ← i.range_eq_compl_range_openComplement_ι] at hy
    obtain ⟨z, hz⟩ := hy
    obtain ⟨F, hF, ⟨w, rfl⟩, hFγ⟩ := h z
    have hxe : Set.range x.base ⊆ Set.range F.e.base := by
      rintro _ ⟨y', rfl⟩
      refine ⟨(F.U.zeroLocusSubschemeι (Set.range F.f)) w, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← F.isPullback.w, Scheme.Hom.comp_apply, hz,
        Subsingleton.elim y' y]
    have he : (L((F.e)^*[ModuleCat.{u + 1} Λ])).map γ =
        (L((F.e)^*[ModuleCat.{u + 1} Λ])).map γ' := by
      have hψ := isIso_supportedRestriction_of_isOpenImmersion Λ F.e i _ F.toZ
        F.isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ F.e c)
      have := hFγ
      simp only [frameRestriction, restrictSupportedClass] at this
      rwa [cancel_epi, cancel_mono] at this
    have hx' := IsOpenImmersion.lift_fac F.e x hxe
    let comp := leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (IsOpenImmersion.lift F.e x hxe)
      F.e x hx'.symm
    rw [← NatIso.naturality_2 comp γ, ← NatIso.naturality_2 comp γ', Functor.comp_map,
      Functor.comp_map, he]

omit [HasKummerClass.IsNormalized Λ] in
/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

*Uniqueness of the fundamental class, for closed immersions with Thom frames.* Two classes in
`H^{2c}_Z(X, Λ(c))` whose restrictions to every Zariski frame agree are equal
(`AlgebraicGeometry.Etale.HasThomFrames.eq_of_forall_exists_frameRestriction_eq`): every point
of `Z` lies in a Zariski frame by `hR`. -/
theorem HasThomFrames.eq_of_frameRestriction_eq (hT : HasThomFrames Λ c i)
    (hR : HasRegularZariskiFrames c i)
    {γ γ' : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))}
    (h : ∀ F : i.EtaleFrame c, IsOpenImmersion F.e →
      frameRestriction Λ F γ = frameRestriction Λ F γ') :
    γ = γ' :=
  hT.eq_of_forall_exists_frameRestriction_eq fun z ↦
    have ⟨F, hF, hz, _⟩ := hR z
    ⟨F, hF, hz, h F hF⟩

/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

**Frame classes agree on overlaps, for closed immersions with Thom frames.** Two frames `F₁`,
`F₂`, with `F₁` given by a weakly regular sequence on an affine scheme, have the same restriction
to any `W` étale over both. Near every point the two frames differ by an invertible matrix, under
which frame classes agree
(`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec_of_field`, which
needs `X` locally of finite type over a field), and the uniqueness of classes applies to the base
change of `i` to `W`, which has Thom frames
(`AlgebraicGeometry.Etale.HasThomFrames.of_isPullback`). -/
theorem HasThomFrames.restrictSupportedClass_frameClass_eq (hT : HasThomFrames Λ c i)
    {k : Type u} [Field k] (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    (F₁ F₂ : i.EtaleFrame c)
    [IsAffine F₁.U] (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(F₁.U, ⊤) (List.ofFn F₁.f))
    {W Z' : Scheme.{u}} [HasInvertibleExponent Λ W] (a : W ⟶ F₁.U) (b : W ⟶ F₂.U)
    [AlgebraicGeometry.Etale a] [AlgebraicGeometry.Etale b] (hab : a ≫ F₁.e = b ≫ F₂.e)
    (i' : Z' ⟶ W) [IsClosedImmersion i']
    (g₁ : Z' ⟶ _) (hg₁ : IsPullback g₁ i' (F₁.U.zeroLocusSubschemeι (Set.range F₁.f)) a)
    (g₂ : Z' ⟶ _) (hg₂ : IsPullback g₂ i' (F₂.U.zeroLocusSubschemeι (Set.range F₂.f)) b) :
    restrictSupportedClass Λ a _ i' g₁ hg₁
        (leftDerivedUpperStarConstantComplexIso Λ a).inv (leftDerivedUpperStarTateShiftIso Λ a c)
        (frameClass Λ F₁) =
      restrictSupportedClass Λ b _ i' g₂ hg₂
        (leftDerivedUpperStarConstantComplexIso Λ b).inv (leftDerivedUpperStarTateShiftIso Λ b c)
        (frameClass Λ F₂) := by
  have hw := hg₁.paste_horiz F₁.isPullback
  have hT' := hT.of_isPullback (a ≫ F₁.e) i' (g₁ ≫ F₁.toZ) hw
  refine hT'.eq_of_forall_exists_frameRestriction_eq fun z ↦ ?_
  obtain ⟨D, hD, hzD⟩ : ∃ D : W.Opens, IsAffineOpen D ∧ i' z ∈ D := by
    obtain ⟨_, ⟨D, hD, rfl⟩, hzD, -⟩ :=
      W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (i' z)) isOpen_univ
    exact ⟨D, hD, hzD⟩
  have : IsAffine D.toScheme := hD
  let v : Fin c → Γ(D.toScheme, ⊤) := fun t ↦ (D.ι ≫ a).appTop (F₁.f t)
  let w : Fin c → Γ(D.toScheme, ⊤) := fun t ↦ (D.ι ≫ b).appTop (F₂.f t)
  have hv : RingTheory.Sequence.IsWeaklyRegular Γ(D.toScheme, ⊤) (List.ofFn v) := by
    have : List.ofFn v = (List.ofFn F₁.f).map (D.ι ≫ a).appTop.hom := by
      rw [List.map_ofFn]; rfl
    rw [this]
    exact hreg.map_of_flat (HasRingHomProperty.appTop @Flat (D.ι ≫ a) inferInstance)
  obtain ⟨gv, hgv⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι (D.ι ≫ a) (Set.range F₁.f)
      (Set.range v) (by rw [← Set.range_comp]; rfl)⟩
  obtain ⟨gw, hgw⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι (D.ι ≫ b) (Set.range F₂.f)
      (Set.range w) (by rw [← Set.range_comp]; rfl)⟩
  have heq : (D.ι ≫ b) ≫ F₂.e = (D.ι ≫ a) ≫ F₁.e := by simp [hab]
  have hspan : Ideal.span (Set.range w) = Ideal.span (Set.range v) :=
    Scheme.span_eq_of_isPullback_zeroLocusSubschemeι (heq ▸ hgw.paste_horiz F₂.isPullback)
      (hgv.paste_horiz F₁.isPullback)
  obtain ⟨M, hM, hdet⟩ := RingTheory.Sequence.IsWeaklyRegular.exists_mulVec_isUnit_det v w hv
    hspan
  -- the point `i' z` of `D` lies in the zero locus of `v`
  obtain ⟨p, hp⟩ : i' z ∈ Set.range D.ι.base := by rw [Scheme.Opens.range_ι]; exact hzD
  have hp0 : p ∈ D.toScheme.zeroLocus (Set.range v) := by
    rw [← Scheme.range_zeroLocusSubschemeι]
    obtain ⟨q, -, hq⟩ := hgv.exists_scheme_point (g₁ z) p (by
      rw [← Scheme.Hom.comp_apply, hg₁.w, Scheme.Hom.comp_apply, ← hp, ← Scheme.Hom.comp_apply])
    exact ⟨q, hq⟩
  -- the frame of `i'` on the basic open of `det M`, given by `v`
  set B := D.toScheme.basicOpen M.det
  obtain ⟨pB, hpB⟩ : p ∈ Set.range B.ι.base := by
    rw [Scheme.Opens.range_ι]; exact Scheme.mem_basicOpen_of_isUnit_mk hdet hp0
  let f : Fin c → Γ(B.toScheme, ⊤) := fun t ↦ B.ι.appTop (v t)
  obtain ⟨gB, hgB⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι B.ι (Set.range v) (Set.range f)
      (by rw [← Set.range_comp]; rfl)⟩
  have hout := hgB.paste_horiz hgv
  let toZ := hg₁.lift (gB ≫ gv) (B.toScheme.zeroLocusSubschemeι (Set.range f) ≫ B.ι ≫ D.ι)
    (by rw [Category.assoc, hgv.w, reassoc_of% hgB.w]; simp)
  have hH : IsPullback toZ (B.toScheme.zeroLocusSubschemeι (Set.range f)) i' (B.ι ≫ D.ι) := by
    refine IsPullback.of_right (h₁₂ := g₁) (v₁₃ := F₁.U.zeroLocusSubschemeι (Set.range F₁.f))
      (h₂₂ := a) ?_ (hg₁.lift_snd _ _ _) hg₁
    rw [hg₁.lift_fst]
    simpa using hout
  let H : i'.EtaleFrame c :=
    { U := B.toScheme
      e := B.ι ≫ D.ι
      etale := inferInstance
      f := f
      toZ := toZ
      isPullback := hH }
  have : HasInvertibleExponent Λ B.toScheme := .of_hom (B.ι ≫ D.ι ≫ a ≫ F₁.e)
  refine ⟨H, inferInstanceAs (IsOpenImmersion (B.ι ≫ D.ι)), ?_, ?_⟩
  · obtain ⟨z', hz', -⟩ := hH.exists_scheme_point z pB (by
      rw [Scheme.Hom.comp_apply, hpB, hp])
    exact ⟨z', hz'⟩
  -- the restriction of the class of `F₁` is the class of `v`
  have h₁ : frameRestriction Λ H (restrictSupportedClass Λ a _ i' g₁ hg₁
      (leftDerivedUpperStarConstantComplexIso Λ a).inv (leftDerivedUpperStarTateShiftIso Λ a c)
      (frameClass Λ F₁)) = kummerBoundaryProduct Λ f := by
    rw [frameRestriction, ← restrictSupportedClass_comp_tateShift Λ H.e a _ rfl _ _ _ g₁ hg₁
      toZ hH (toZ ≫ g₁) (hH.paste_horiz hg₁)]
    exact restrictSupportedClass_kummerBoundaryProduct Λ _ F₁.f f (fun _ ↦ rfl) _ _
  -- the restriction of the class of `F₂` is the class of `M v`, hence of `v`
  let w' : Fin c → Γ(B.toScheme, ⊤) := fun t ↦ B.ι.appTop (w t)
  let M' := M.map B.ι.appTop.hom
  have hw' : w' = M'.mulVec f := by
    funext t
    simp only [w', f, M', hM, RingHom.map_mulVec]
    rfl
  have hdet' : IsUnit M'.det := by
    rw [show M'.det = _ from (RingHom.map_det B.ι.appTop.hom M).symm]
    refine B.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun y _ ↦ ?_
    rw [← B.toScheme.mem_basicOpen_top, ← Scheme.preimage_basicOpen_top]
    exact y.2
  obtain ⟨gw', hgw'⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι (H.e ≫ b) (Set.range F₂.f)
      (Set.range w') (by rw [← Set.range_comp]; rfl)⟩
  obtain ⟨g₀, hg₀⟩ := Scheme.exists_isPullback_zeroLocusSubschemeι_of_span_eq
    (U := B.toScheme) (s := Set.range w') (s' := Set.range f)
    (by rw [hw', Ideal.span_range_mulVec_of_isUnit_det _ hdet'])
  have key : ∀ (w'' : Fin c → Γ(B.toScheme, ⊤)) (_ : w'' = M'.mulVec f) (g : _ ⟶ _)
      (hg : IsPullback g (B.toScheme.zeroLocusSubschemeι (Set.range f))
        (B.toScheme.zeroLocusSubschemeι (Set.range w'')) (𝟙 _)),
      restrictSupportedClass Λ (𝟙 _) _ _ g hg
        (leftDerivedUpperStarConstantComplexIso Λ (𝟙 _)).inv
        (leftDerivedUpperStarTateShiftIso Λ (𝟙 _) c) (kummerBoundaryProduct Λ w'') =
      kummerBoundaryProduct Λ f := by
    rintro _ rfl g hg
    have : IsAffine B.toScheme := (isAffineOpen_top D.toScheme).basicOpen M.det
    exact restrictSupportedClass_kummerBoundaryProduct_mulVec_of_field Λ
      (B.ι ≫ D.ι ≫ a ≫ F₁.e ≫ aX) f M' hdet' g hg
  have h₂ : frameRestriction Λ H (restrictSupportedClass Λ b _ i' g₂ hg₂
      (leftDerivedUpperStarConstantComplexIso Λ b).inv (leftDerivedUpperStarTateShiftIso Λ b c)
      (frameClass Λ F₂)) = kummerBoundaryProduct Λ f := by
    rw [frameRestriction, ← restrictSupportedClass_comp_tateShift Λ H.e b _ rfl _ _ _ g₂ hg₂
      toZ hH (toZ ≫ g₂) (hH.paste_horiz hg₂),
      restrictSupportedClass_comp_tateShift Λ (𝟙 _) (H.e ≫ b) _ (Category.id_comp _).symm _ _ _
      gw' hgw'
      g₀ hg₀ (toZ ≫ g₂) (hH.paste_horiz hg₂)]
    rw [frameClass, restrictSupportedClass_kummerBoundaryProduct Λ _ F₂.f w' (fun _ ↦ rfl) _ _]
    exact key w' hw' g₀ hg₀
  rw [h₁, h₂]

/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

**(b) The fundamental class, for closed immersions with Thom frames.** Let `i : Z ⟶ X` be a
closed immersion with Thom frames and regular Zariski frames of codimension `c`, with `X` locally
of finite type over a field `k`. The frame classes depend only on `Z_U ⊂ U`, not on the frame,
and they glue: there is a unique class `[Z ⊂ X] ∈ H^{2c}_Z(X, Λ(c))` whose restriction to every
frame is the frame class.

Near every point of `Z` there is a frame given by a regular sequence on an affine open, and any
other frame differs from it, near `Z`, by a matrix with invertible determinant
(`RingTheory.Sequence.IsWeaklyRegular.exists_mulVec_isUnit_det`), under which the frame classes
agree (`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec_of_field`); so
frame classes agree on overlaps
(`AlgebraicGeometry.Etale.HasThomFrames.restrictSupportedClass_frameClass_eq`). By (a)
(`AlgebraicGeometry.Etale.HasThomFrames.isZero_homology_rightDerivedLowerShriek`) the classes are
morphisms into a sheaf placed in degree zero, so the Zariski-local classes glue
(`AlgebraicGeometry.Etale.exists_hom_of_isOpenImmersion_cover`). -/
theorem HasThomFrames.existsUnique_fundamentalClass (hT : HasThomFrames Λ c i)
    (hR : HasRegularZariskiFrames c i) {k : Type u} [Field k] (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] :
    ∃! γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)),
      ∀ F : i.EtaleFrame c, frameRestriction Λ F γ = frameClass Λ F := by
  obtain ⟨G, ⟨eM⟩⟩ := hT.exists_iso_singleFunctor_rightDerivedLowerShriek
  choose F hFo hzF hFa hFr using id hR
  have hdisj : Disjoint (Set.range i.base) (Set.range i.openComplement.ι.base) := by
    rw [i.range_eq_compl_range_openComplement_ι]
    exact disjoint_compl_left
  -- the cover of `X` by the Zariski frames and the complement of `Z`
  let V : Option Z → Scheme.{u} := fun j ↦ Option.elim j i.openComplement.toScheme (F · |>.U)
  let e : ∀ j, V j ⟶ X := fun j ↦ match j with
    | none => i.openComplement.ι
    | some z => (F z).e
  have he : ∀ j, IsOpenImmersion (e j) := by
    rintro (_ | z)
    · exact inferInstanceAs (IsOpenImmersion i.openComplement.ι)
    · exact hFo z
  have hΨ : ∀ z, IsIso (supportedRestriction Λ (F z).e i _ (F z).toZ
      (F z).isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ (F z).e c)) := fun z ↦
    have := hFo z
    isIso_supportedRestriction_of_isOpenImmersion _ _ _ _ _ _ _ _ _
  let δ : ∀ j, (L((e j)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X) ⟶
      (L((e j)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))) :=
    fun j ↦ match j with
    | none => 0
    | some z => (leftDerivedUpperStarConstantComplexIso Λ (F z).e).hom ≫ frameClass Λ (F z) ≫
        inv (supportedRestriction Λ (F z).e i _ (F z).toZ
          (F z).isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ (F z).e c))
  have hδ : ∀ z, δ (some z) ≫ supportedRestriction Λ (F z).e i _ (F z).toZ
      (F z).isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ (F z).e c) =
        (leftDerivedUpperStarConstantComplexIso Λ (F z).e).hom ≫ frameClass Λ (F z) := by
    intro z
    simp [δ]
  -- the restriction of `Ri_! Ri^! (Λ(c)[2c])` to the complement of `Z` vanishes
  have hzero : ∀ {W : Scheme.{u}} (w : W ⟶ X),
      Set.range w.base ⊆ Set.range i.openComplement.ι.base →
      IsZero ((L((w)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)))) :=
    fun w hw ↦ isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint _ i
      i.openComplement.ι hdisj w hw _
  have hcov : ∀ x : X, ∃ j, x ∈ Set.range (e j).base := by
    intro x
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨w, hw⟩ := hzF z
      refine ⟨some z, (F z).U.zeroLocusSubschemeι _ w, ?_⟩
      change (F z).e _ = i z
      rw [← Scheme.Hom.comp_apply, ← (F z).isPullback.w, Scheme.Hom.comp_apply, hw]
    · refine ⟨none, ?_⟩
      rwa [← Set.mem_compl_iff, i.range_eq_compl_range_openComplement_ι, compl_compl] at hx
  obtain ⟨γ, hγ⟩ := exists_hom_of_isOpenImmersion_cover (constantComplexIsoSingleFunctor Λ X) eM
    e hcov δ (by
    rintro (_ | z) (_ | z') W a b _ _ h
    · exact (hzero _ (by rintro _ ⟨y, rfl⟩; exact ⟨a y, rfl⟩)).eq_of_tgt _ _
    · exact (hzero _ (by rintro _ ⟨y, rfl⟩; exact ⟨a y, rfl⟩)).eq_of_tgt _ _
    · exact (hzero _ (by rw [h]; rintro _ ⟨y, rfl⟩; exact ⟨b y, rfl⟩)).eq_of_tgt _ _
    · -- two Zariski frames: compare the restrictions of the frame classes to `W`
      have := hFo z
      have := hFo z'
      have := hFa z
      change W ⟶ (F z).U at a
      change W ⟶ (F z').U at b
      change a ≫ (F z).e = b ≫ (F z').e at h
      have : HasInvertibleExponent Λ W := .of_hom a
      obtain ⟨g₁, hg₁⟩ : ∃ g, IsPullback g _ _ _ :=
        ⟨_, isPullback_zeroLocusSubschemeι a (Set.range (F z).f)
          (Set.range fun t ↦ a.appTop ((F z).f t)) (by rw [← Set.range_comp]; rfl)⟩
      have hg' := hg₁.paste_horiz (F z).isPullback
      have hout : IsPullback (g₁ ≫ (F z).toZ)
          (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((F z).f t))) i (b ≫ (F z').e) :=
        h ▸ hg'
      let g₂ := (F z').isPullback.lift (g₁ ≫ (F z).toZ)
        (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((F z).f t)) ≫ b)
        (by rw [hout.w, Category.assoc])
      have hg₂ : IsPullback g₂ (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((F z).f t)))
          _ b :=
        IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hout)
          ((F z').isPullback.lift_snd _ _ _)
          (F z').isPullback
      have := isIso_supportedRestriction_of_isOpenImmersion Λ (a ≫ (F z).e) i
        _ _ hg' _ _ (leftDerivedUpperStarTateShiftIso Λ (a ≫ (F z).e) c)
      rw [← cancel_epi (leftDerivedUpperStarConstantComplexIso Λ (a ≫ (F z).e)).inv,
        ← cancel_mono (supportedRestriction Λ (a ≫ (F z).e) i _ _ hg' _ _
          (leftDerivedUpperStarTateShiftIso Λ (a ≫ (F z).e) c))]
      simp only [Category.assoc]
      exact (constantComplexIso_inv_comp_leftDerivedUpperStarComp_map_supportedRestriction Λ
        (F z).e a _ rfl i _ _ (F z).toZ (F z).isPullback g₁ hg₁ _ hg' _ _ (hδ z)).trans
          ((hT.restrictSupportedClass_frameClass_eq aX (F z) (F z') (hFr z) a b h _ g₁ hg₁
            g₂ hg₂).trans
          (constantComplexIso_inv_comp_leftDerivedUpperStarComp_map_supportedRestriction Λ
            (F z').e b _ h i _ _ (F z').toZ (F z').isPullback g₂ hg₂ _ hg' _ _ (hδ z')).symm))
  have hγz : ∀ z, frameRestriction Λ (F z) γ = frameClass Λ (F z) := by
    intro z
    have h : (L(((F z).e)^*[ModuleCat.{u + 1} Λ])).map γ = δ (some z) := hγ (some z)
    simp only [frameRestriction, restrictSupportedClass, h, δ, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, Iso.inv_hom_id_assoc]
  -- every frame is compared with the Zariski frames near each of its points
  have hall : ∀ F' : i.EtaleFrame c, frameRestriction Λ F' γ = frameClass Λ F' := by
    intro F'
    have hT' := hT.of_isPullback F'.e _ F'.toZ F'.isPullback
    refine hT'.eq_of_forall_exists_frameRestriction_eq fun z' ↦ ?_
    set z := F'.toZ z'
    have := hFo z
    have := hFa z
    let W : F'.U.Opens := F'.e ⁻¹ᵁ (F z).e.opensRange
    have hrange : Set.range (W.ι ≫ F'.e).base ⊆ Set.range (F z).e.base := by
      rintro _ ⟨y, rfl⟩
      exact y.2
    let a := IsOpenImmersion.lift (F z).e (W.ι ≫ F'.e) hrange
    have hab : a ≫ (F z).e = W.ι ≫ F'.e := IsOpenImmersion.lift_fac _ _ _
    have : AlgebraicGeometry.Etale (a ≫ (F z).e) := hab ▸ inferInstance
    have : AlgebraicGeometry.Etale a := .of_comp a (F z).e
    let H := Scheme.Hom.EtaleFrame.ofFunctions F'.f W.ι
    have hout : IsPullback (H.toZ ≫ F'.toZ) (W.toScheme.zeroLocusSubschemeι (Set.range H.f)) i
        (a ≫ (F z).e) := hab ▸ H.isPullback.paste_horiz F'.isPullback
    let g₁ := (F z).isPullback.lift (H.toZ ≫ F'.toZ)
      (W.toScheme.zeroLocusSubschemeι (Set.range H.f) ≫ a) (by rw [hout.w, Category.assoc])
    have hg₁ : IsPullback g₁ (W.toScheme.zeroLocusSubschemeι (Set.range H.f)) _ a :=
      IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hout)
        ((F z).isPullback.lift_snd _ _ _) (F z).isPullback
    refine ⟨H, inferInstanceAs (IsOpenImmersion W.ι), ?_, ?_⟩
    · obtain ⟨w₀, hw₀⟩ := hzF z
      obtain ⟨p, hp⟩ : (F'.U.zeroLocusSubschemeι (Set.range F'.f)) z' ∈ Set.range W.ι.base := by
        rw [Scheme.Opens.range_ι]
        refine ⟨(F z).U.zeroLocusSubschemeι _ w₀, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← (F z).isPullback.w, Scheme.Hom.comp_apply, hw₀,
          ← Scheme.Hom.comp_apply, F'.isPullback.w, Scheme.Hom.comp_apply]
      obtain ⟨q, hq, -⟩ := H.isPullback.exists_scheme_point z' p hp.symm
      exact ⟨q, hq⟩
    · have e₁ := restrictSupportedClass_comp_tateShift Λ W.ι F'.e (W.ι ≫ F'.e) rfl _ _ _ F'.toZ
        F'.isPullback H.toZ H.isPullback _ (H.isPullback.paste_horiz F'.isPullback) γ
      have e₂ := restrictSupportedClass_comp_tateShift Λ a (F z).e (W.ι ≫ F'.e) hab.symm _ _ _
        (F z).toZ (F z).isPullback g₁ hg₁ _ (H.isPullback.paste_horiz F'.isPullback) γ
      have e₃ := hT.restrictSupportedClass_frameClass_eq aX (F z) F' (hFr z) a W.ι hab _ g₁
        hg₁ H.toZ H.isPullback
      exact e₁.symm.trans (e₂.trans ((congrArg (restrictSupportedClass _ a _ _ g₁ hg₁ _ _)
        (hγz z)).trans e₃))
  exact ⟨γ, hall, fun γ' hγ' ↦ hT.eq_of_frameRestriction_eq hR fun F _ ↦ by
    rw [hγ' F, hall F]⟩


variable (Λ)

/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

The *fundamental class* `[Z ⊂ X] = cl_{Z/X} ∈ H^{2c}_Z(X, Λ(c))` of a closed immersion
`i : Z ⟶ X` with Thom frames and regular Zariski frames of codimension `c`, with `X` locally of
finite type over a field: the unique class restricting to the frame class
`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` on every frame.

It is *defined* as `Classical.choose` of
`AlgebraicGeometry.Etale.HasThomFrames.existsUnique_fundamentalClass`; uniqueness is what makes
the choice canonical. -/
noncomputable def thomFundamentalClass (hT : HasThomFrames Λ c i)
    (hR : HasRegularZariskiFrames c i) {k : Type u} [Field k] (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] :
    constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) :=
  (hT.existsUnique_fundamentalClass hR aX).exists.choose

/-- The fundamental class `AlgebraicGeometry.Etale.thomFundamentalClass` restricts to the frame
class on every frame. -/
theorem frameRestriction_thomFundamentalClass (hT : HasThomFrames Λ c i)
    (hR : HasRegularZariskiFrames c i) {k : Type u} [Field k] (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] (F : i.EtaleFrame c) :
    frameRestriction Λ F (thomFundamentalClass Λ hT hR aX) = frameClass Λ F :=
  (hT.existsUnique_fundamentalClass hR aX).exists.choose_spec F

/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

The morphism `cl_i : Λ_Z ⟶ Ri^! (Λ_X(c)[2c])`, `1 ↦ [Z ⊂ X]`, for a closed immersion with Thom
frames: the adjoint (`AlgebraicGeometry.Etale.supportedClassMap`) of the fundamental class
`AlgebraicGeometry.Etale.thomFundamentalClass`. -/
noncomputable def thomFundamentalClassMap (hT : HasThomFrames Λ c i)
    (hR : HasRegularZariskiFrames c i) {k : Type u} [Field k] (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] :
    constantComplex Λ Z ⟶ (R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) :=
  supportedClassMap Λ i (thomFundamentalClass Λ hT hR aX)

/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

**(c) `cl_i` is an isomorphism, for closed immersions with Thom frames.** On a Thom frame
`(e : U ⟶ X, f)`, the fundamental class restricts to the frame class
(`AlgebraicGeometry.Etale.frameRestriction_thomFundamentalClass`), whose adjoint is an
isomorphism; restriction of supports along the étale `e` being invertible, the restriction of
`cl_i` to `V(f) ⟶ Z` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_restrictSupportedClass_iff`), and these
restrictions detect isomorphisms on cohomology sheaves. -/
theorem isIso_thomFundamentalClassMap (hT : HasThomFrames Λ c i)
    (hR : HasRegularZariskiFrames c i) {k : Type u} [Field k] (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] :
    IsIso (thomFundamentalClassMap Λ hT hR aX) := by
  have hloc : ∀ z : Z, ∃ F : i.EtaleFrame c, z ∈ Set.range F.toZ ∧
      IsIso ((L((F.toZ)^*[ModuleCat.{u + 1} Λ])).map (thomFundamentalClassMap Λ hT hR aX)) := by
    intro z
    obtain ⟨F, hz, hF⟩ := hT z
    rw [← frameRestriction_thomFundamentalClass Λ hT hR aX F, frameRestriction] at hF
    have hψe := isIso_supportedRestriction_of_etale Λ F.e i _ F.toZ F.isPullback
      ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) ((tateObject Λ F.U c)⟦2 * (c : ℤ)⟧)
      (leftDerivedUpperStarTateShiftIso Λ F.e c)
    exact ⟨F, hz,
      (isIso_supportedClassMap_restrictSupportedClass_iff Λ F.e _ _ _ F.isPullback _ _ _ _
        hψe).1 hF⟩
  choose F hzF hF using hloc
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (fun z ↦ (F z).toZ) (fun z ↦ ⟨z, hzF z⟩) _ fun z ↦ ?_
  have h : IsIso (D(((F z).toZ)^*[ModuleCat.{u + 1} Λ]).map
      (thomFundamentalClassMap Λ hT hR aX)) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ (F z).toZ) _).1 (hF z)
  exact (NatIso.isIso_map_iff
    ((((F z).toZ)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n) _).2
    (Functor.map_isIso (_root_.DerivedCategory.homologyFunctor _ n)
      (D(((F z).toZ)^*[ModuleCat.{u + 1} Λ]).map (thomFundamentalClassMap Λ hT hR aX)))

/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

**Purity for closed immersions with Thom frames**, `Ri^! (Λ_X(c)[2c]) ≅ Λ_Z`, for a closed
immersion `i : Z ⟶ X` with Thom frames and regular Zariski frames of codimension `c`, with `X`
locally of finite type over a field: the inverse of `cl_i`
(`AlgebraicGeometry.Etale.isIso_thomFundamentalClassMap`). Unlike
the purity theorem for regular immersions over a perfect field, which is
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_shiftTateObject_of_isRegularImmersion`
and is derived from smooth purity, this does not use smooth purity. -/
theorem nonempty_iso_rightDerivedUpperShriek_tateObject_of_hasThomFrames
    (hT : HasThomFrames Λ c i) (hR : HasRegularZariskiFrames c i) {k : Type u} [Field k]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] :
    Nonempty ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) ≅ constantComplex Λ Z) :=
  have := isIso_thomFundamentalClassMap Λ hT hR aX
  ⟨(asIso (thomFundamentalClassMap Λ hT hR aX)).symm⟩

end Etale

end AlgebraicGeometry
