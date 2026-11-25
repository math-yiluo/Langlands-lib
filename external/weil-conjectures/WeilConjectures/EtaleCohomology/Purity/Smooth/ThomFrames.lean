/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionFrame
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion
public import WeilConjectures.SixFunctors.Integral.Exact
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale

/-!
# Closed immersions with Thom frames

A closed immersion `i : Z ⟶ X` *has Thom frames* of codimension `c`
(`AlgebraicGeometry.Etale.HasThomFrames`) if every point of `Z` lies in the zero locus of an
étale frame `(e : U ⟶ X, f₁, …, f_c)` (`AlgebraicGeometry.Scheme.Hom.EtaleFrame`) whose frame
class `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` is a Thom class: its adjoint `Λ ⟶ R i_U^! (Λ(c)[2c])` is an
isomorphism. This holds for closed immersions which are étale-locally the zero section of
affine space over a base separated and locally of finite type over a field
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_coord_of_field`), e.g.
the diagonal of a smooth morphism.

This is the input replacing smooth purity in clause (a) of blueprint `lemma-class-of-point--1`: for
such `i`, the object `Ri_! Ri^! (Λ_X(c)[2c])` is concentrated in degree zero, as it becomes
`Ri_{U!} Λ` on every Thom frame and vanishes off `Z`.

## Main definitions

- `AlgebraicGeometry.Etale.HasThomFrames`: `i` has Thom frames.
- `AlgebraicGeometry.Etale.HasRegularZariskiFrames`: every point of `Z` lies in a Zariski frame
  given by a weakly regular sequence on an affine open.

## Main statements

- `AlgebraicGeometry.Etale.HasThomFrames.of_isPullback`: stability under étale base change.
- `AlgebraicGeometry.Etale.HasThomFrames.isZero_homology_rightDerivedLowerShriek`: clause (a).
- `AlgebraicGeometry.Etale.HasThomFrames.exists_iso_singleFunctor_rightDerivedLowerShriek`:
  classes with supports are sections of a sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- For a closed immersion `j`, the object `Rj_! Λ = j_* Λ` has no cohomology sheaves outside
degree `0`: `j_*` is exact. -/
lemma isZero_homology_rightDerivedLowerShriek_constantComplex {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (n : ℤ) (hn : n ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R(j)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z))) := by
  set K := constantComplex Λ Z
  have : K.IsGE 0 := (_root_.DerivedCategory.isGE_iff K 0).2 fun n hn ↦
    isZero_homology_constantComplex Λ _ n hn.ne
  have : K.IsLE 0 := (_root_.DerivedCategory.isLE_iff K 0).2 fun n hn ↦
    isZero_homology_constantComplex Λ _ n hn.ne'
  have := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom Λ j
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) j
  have h₁ : (((j)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K).IsGE 0 :=
    ((j)_*[ModuleCat.{u + 1} Λ]).isGE_mapDerivedCategory_obj K 0
  have h₂ : (((j)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K).IsLE 0 :=
    ((j)_*[ModuleCat.{u + 1} Λ]).isLE_mapDerivedCategory_obj K 0
  have E := (_root_.DerivedCategory.homologyFunctor _ n).mapIso (e.app K ≪≫
    ((j)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorIsoMapDerivedCategory.app K)
  rcases lt_or_gt_of_ne hn with hn | hn
  · exact ((_root_.DerivedCategory.isGE_iff _ 0).1 h₁ n hn).of_iso E
  · exact ((_root_.DerivedCategory.isLE_iff _ 0).1 h₂ n hn).of_iso E

variable [Finite Λ] [HasKummerClass Λ] {X Z : Scheme.{u}} (c : ℕ)
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- A closed immersion `i : Z ⟶ X` *has Thom frames* of codimension `c`: every point of `Z` lies
in the zero locus of an étale frame (`AlgebraicGeometry.Scheme.Hom.EtaleFrame`) whose frame
class is a Thom class, i.e. has invertible adjoint `Λ ⟶ R i_F^! (Λ(c)[2c])`
(`AlgebraicGeometry.Etale.supportedClassMap`). This is the local input of clause (a) of blueprint
`lemma-class-of-point--1`. -/
def HasThomFrames [HasInvertibleExponent Λ X] : Prop :=
  ∀ z : Z, ∃ F : i.EtaleFrame c, z ∈ Set.range F.toZ ∧
    IsIso (supportedClassMap Λ (F.U.zeroLocusSubschemeι (Set.range F.f)) (frameClass Λ F))

/-- A closed immersion `i : Z ⟶ X` *has regular Zariski frames* of codimension `c`: every point
of `Z` lies in the zero locus of a Zariski frame of `i` given by a weakly regular sequence of
`c` functions on an affine open of `X` (blueprint `lemma-class-of-point--1`). -/
def HasRegularZariskiFrames : Prop :=
  ∀ z : Z, ∃ F : i.EtaleFrame c, IsOpenImmersion F.e ∧ z ∈ Set.range F.toZ ∧ IsAffine F.U ∧
    RingTheory.Sequence.IsWeaklyRegular Γ(F.U, ⊤) (List.ofFn F.f)

variable {Λ c i}

omit [IsClosedImmersion i] in
/-- **Thom frames are stable under étale base change.** If `i` has Thom frames, so does its base
change `i'` along an étale `e : X' ⟶ X`: a frame `(U, f)` of `i` pulls back to the frame
`(U ×_X X', f)` of `i'`, whose frame class is the restriction of that of `(U, f)`, and the
adjoint of the restricted class is an isomorphism, restriction of supports along the étale
`U ×_X X' ⟶ U` being invertible. -/
theorem HasThomFrames.of_isPullback [HasInvertibleExponent Λ X] (hT : HasThomFrames Λ c i)
    {X' Z' : Scheme.{u}} (e : X' ⟶ X) [AlgebraicGeometry.Etale e] (i' : Z' ⟶ X')
    [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e) :
    haveI : HasInvertibleExponent Λ X' := .of_hom e
    HasThomFrames Λ c i' := by
  have : HasInvertibleExponent Λ X' := .of_hom e
  intro z'
  obtain ⟨F, ⟨w, hw⟩, hF⟩ := hT (g z')
  let a := pullback.fst F.e e
  have : HasInvertibleExponent Λ (pullback F.e e) := .of_hom a
  let f' : Fin c → Γ(pullback F.e e, ⊤) := fun t ↦ a.appTop (F.f t)
  obtain ⟨g₁, hg₁⟩ : ∃ g, IsPullback g ((pullback F.e e).zeroLocusSubschemeι (Set.range f'))
      (F.U.zeroLocusSubschemeι (Set.range F.f)) a :=
    ⟨_, isPullback_zeroLocusSubschemeι a (Set.range F.f) (Set.range f')
      (by rw [← Set.range_comp]; rfl)⟩
  have hout : IsPullback (g₁ ≫ F.toZ) ((pullback F.e e).zeroLocusSubschemeι (Set.range f')) i
      (pullback.snd F.e e ≫ e) := by
    rw [← pullback.condition]; exact hg₁.paste_horiz F.isPullback
  let toZ := hg.lift (g₁ ≫ F.toZ)
    ((pullback F.e e).zeroLocusSubschemeι (Set.range f') ≫ pullback.snd F.e e)
    (by rw [hout.w, Category.assoc])
  have hH : IsPullback toZ ((pullback F.e e).zeroLocusSubschemeι (Set.range f')) i'
      (pullback.snd F.e e) :=
    IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hout) (hg.lift_snd _ _ _) hg
  let F' : i'.EtaleFrame c :=
    { U := pullback F.e e
      e := pullback.snd F.e e
      etale := inferInstance
      f := f'
      toZ := toZ
      isPullback := hH }
  refine ⟨F', ?_, ?_⟩
  · obtain ⟨p, hp₁, hp₂⟩ := (IsPullback.of_hasPullback F.e e).exists_scheme_point
      (F.U.zeroLocusSubschemeι (Set.range F.f) w) (i' z') (by
        rw [← Scheme.Hom.comp_apply, ← F.isPullback.w, Scheme.Hom.comp_apply, hw,
          ← Scheme.Hom.comp_apply, hg.w, Scheme.Hom.comp_apply])
    obtain ⟨q, hq, -⟩ := hH.exists_scheme_point z' p hp₂.symm
    exact ⟨q, hq⟩
  · have h₁ : frameClass Λ F' = restrictSupportedClass Λ a _ _ g₁ hg₁
        (leftDerivedUpperStarConstantComplexIso Λ a).inv
        (leftDerivedUpperStarTateShiftIso Λ a c) (frameClass Λ F) :=
      (restrictSupportedClass_kummerBoundaryProduct Λ a F.f f' (fun _ ↦ rfl) g₁ hg₁).symm
    have hψ := isIso_supportedRestriction_of_etale Λ a _ _ g₁ hg₁
      ((tateObject Λ F.U c)⟦2 * (c : ℤ)⟧) ((tateObject Λ (pullback F.e e) c)⟦2 * (c : ℤ)⟧)
      (leftDerivedUpperStarTateShiftIso Λ a c)
    change IsIso (supportedClassMap Λ _ (frameClass Λ F'))
    rw [h₁]
    exact (isIso_supportedClassMap_restrictSupportedClass_iff Λ a _ _ g₁ hg₁ _ _ _ _ hψ).2
      inferInstance

attribute [local instance] HasInvertibleExponent.opens

/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

**(a) Concentration in degree zero, for closed immersions with Thom frames.** If `i` has Thom
frames, then `Ri_! Ri^! (Λ_X(c)[2c])` has no cohomology sheaves outside degree `0`. Off `Z` it
vanishes; on a Thom frame `(e : U ⟶ X, f)` it becomes `Ri_{U!} Ri_U^! (Λ_U(c)[2c])`
(`AlgebraicGeometry.Etale.isIso_supportedRestriction_of_etale`), which is `Ri_{U!} Λ` through the
adjoint of the frame class, and `Ri_{U!} = i_{U*}` is exact. -/
theorem HasThomFrames.isZero_homology_rightDerivedLowerShriek [HasInvertibleExponent Λ X]
    (hT : HasThomFrames Λ c i) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj
        ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)))) := by
  choose F hzF hF using hT
  set M := (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj
    ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))
  have hdisj : Disjoint (Set.range i.base) (Set.range i.openComplement.ι.base) := by
    rw [i.range_eq_compl_range_openComplement_ι]
    exact disjoint_compl_left
  let V : Option Z → Scheme.{u} := fun j ↦ Option.elim j i.openComplement.toScheme (F · |>.U)
  let e : ∀ j, V j ⟶ X := fun j ↦ match j with
    | none => i.openComplement.ι
    | some z => (F z).e
  have hcov : ∀ x : X, ∃ (j : Option Z) (y : V j), (e j).base y = x := by
    intro x
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨w, hw⟩ := hzF z
      refine ⟨some z, (F z).U.zeroLocusSubschemeι _ w, ?_⟩
      change (F z).e _ = i z
      rw [← Scheme.Hom.comp_apply, ← (F z).isPullback.w, Scheme.Hom.comp_apply, hw]
    · rw [← Set.mem_compl_iff, i.range_eq_compl_range_openComplement_ι, compl_compl] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨none, y, hy⟩
  have hloc : ∀ j, IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((L((e j)^*[ModuleCat.{u + 1} Λ])).obj M)) := by
    rintro (_ | z)
    · exact Functor.map_isZero _
        (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint _ i
          i.openComplement.ι hdisj i.openComplement.ι subset_rfl _)
    · have hψ := isIso_supportedRestriction_of_etale Λ (F z).e i _ (F z).toZ (F z).isPullback
        ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) ((tateObject Λ (F z).U c)⟦2 * (c : ℤ)⟧)
        (leftDerivedUpperStarTateShiftIso Λ (F z).e c)
      have := hF z
      exact (isZero_homology_rightDerivedLowerShriek_constantComplex Λ _ n hn).of_iso
        ((_root_.DerivedCategory.homologyFunctor _ n).mapIso
          (asIso (supportedRestriction Λ (F z).e i _ (F z).toZ (F z).isPullback _ _
            (leftDerivedUpperStarTateShiftIso Λ (F z).e c)) ≪≫
          (R((F z).U.zeroLocusSubschemeι (Set.range (F z).f))_![ModuleCat.{u + 1} Λ]).mapIso
            (asIso (supportedClassMap Λ _ (frameClass Λ (F z)))).symm))
  have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) e hcov
    (0 : (_root_.DerivedCategory.homologyFunctor _ n).obj M ⟶ 0) fun j ↦
      isIso_of_source_target_iso_zero _
        ((hloc j).of_iso
          (((e j)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryHomologyFunctorIso n).app M ≪≫
            (_root_.DerivedCategory.homologyFunctor _ n).mapIso
              ((leftDerivedUpperStarIsoMapDerivedCategory _ (e j)).symm.app M))).isoZero
        (Functor.map_isZero _ (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso
    (asIso (0 : (_root_.DerivedCategory.homologyFunctor _ n).obj M ⟶ 0))

/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

For a closed immersion with Thom frames, classes with supports `H^{2c}_Z(X, Λ(c))` are sections
of a sheaf: `Ri_! Ri^! (Λ_X(c)[2c])` is a sheaf placed in degree zero
(`AlgebraicGeometry.Etale.HasThomFrames.isZero_homology_rightDerivedLowerShriek`). -/
theorem HasThomFrames.exists_iso_singleFunctor_rightDerivedLowerShriek
    [HasInvertibleExponent Λ X] (hT : HasThomFrames Λ c i) :
    ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Nonempty ((R(i)_![ModuleCat.{u + 1} Λ]).obj
          ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj G) := by
  set M := (R(i)_![ModuleCat.{u + 1} Λ]).obj
    ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))
  have hM := hT.isZero_homology_rightDerivedLowerShriek
  have : M.IsGE 0 := (_root_.DerivedCategory.isGE_iff M 0).2 fun n hn ↦ hM n hn.ne
  have : M.IsLE 0 := (_root_.DerivedCategory.isLE_iff M 0).2 fun n hn ↦ hM n hn.ne'
  exact _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE M 0

end Etale

end AlgebraicGeometry
