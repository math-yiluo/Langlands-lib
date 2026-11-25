/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomFramesFundamentalClass

/-!
# Transport of the Thom fundamental class along an étale base change

Let `i : Z ⟶ X` be a closed immersion with Thom frames and `i' : Z' ⟶ X'` its base change along
an étale morphism `e : X' ⟶ X` (for instance an isomorphism). The restriction of supports of the
fundamental class `[Z ⊂ X]` (`AlgebraicGeometry.Etale.thomFundamentalClass`) along `e` is the
fundamental class `[Z' ⊂ X']`
(`AlgebraicGeometry.Etale.restrictSupportedClass_thomFundamentalClass_of_etale`): a frame
`(U, e', f)` of
`i'` is a frame `(U, e' ≫ e, f)` of `i` (`AlgebraicGeometry.Scheme.Hom.EtaleFrame.ofIsPullback`),
with the same frame class, and restriction of supports along the composite `e' ≫ e` is the
composite of the restrictions, so the restricted fundamental class has the frame classes as frame
restrictions, which characterizes `[Z' ⊂ X']` (`HasThomFrames.existsUnique_fundamentalClass`).
This is the first step of the base change compatibility of the canonical orientation of a smooth
morphism along an isomorphism of pairs (blueprint `proposition-compatibility-purity-base-change`,
the Frobenius square).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  {X X' Z Z' : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ X'] {c : ℕ}
  {i : Z ⟶ X} {i' : Z' ⟶ X'} [IsClosedImmersion i] [IsClosedImmersion i']
  (e : X' ⟶ X) [AlgebraicGeometry.Etale e] {g : Z' ⟶ Z} (hg : IsPullback g i' i e)

/-- The restriction to a frame `F` of `i'` of the restriction of supports along `e` of a class
`γ` with supports on `Z` is the restriction of `γ` to the frame `(U, F.e ≫ e, f)` of `i`. -/
lemma frameRestriction_restrictSupportedClass (F : i'.EtaleFrame c)
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))) :
    frameRestriction Λ F (restrictSupportedClass Λ e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv (leftDerivedUpperStarTateShiftIso Λ e c)
        γ) =
      frameRestriction Λ (Scheme.Hom.EtaleFrame.ofIsPullback hg F) γ := by
  unfold frameRestriction
  symm
  exact restrictSupportedClass_comp_tateShift Λ F.e e (F.e ≫ e) rfl i i' _ g hg F.toZ
    F.isPullback (F.toZ ≫ g) (F.isPullback.paste_horiz hg) γ

/-- **The fundamental class is compatible with étale base change**: the restriction of supports
along `e` of the fundamental class of `i` is the fundamental class of its base change `i'`. -/
theorem restrictSupportedClass_thomFundamentalClass_of_etale [HasKummerClass.IsNormalized Λ]
    (hT : HasThomFrames Λ c i) (hR : HasRegularZariskiFrames c i)
    (hT' : HasThomFrames Λ c i') (hR' : HasRegularZariskiFrames c i')
    {k k' : Type u} [Field k] [Field k'] (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    (aX' : X' ⟶ Spec (.of k')) [LocallyOfFiniteType aX'] :
    restrictSupportedClass Λ e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv (leftDerivedUpperStarTateShiftIso Λ e c)
        (thomFundamentalClass Λ hT hR aX) =
      thomFundamentalClass Λ hT' hR' aX' :=
  (hT'.existsUnique_fundamentalClass hR' aX').unique
    (fun F ↦ by
      rw [frameRestriction_restrictSupportedClass, frameRestriction_thomFundamentalClass]
      rfl)
    (frameRestriction_thomFundamentalClass Λ hT' hR' aX')

/-- **The purity map `cl_i` is compatible with étale base change**, on the fundamental classes:
`cl_{i'}` is the adjoint of the restricted fundamental class. -/
theorem thomFundamentalClassMap_eq_supportedClassMap_restrictSupportedClass
    [HasKummerClass.IsNormalized Λ]
    (hT : HasThomFrames Λ c i) (hR : HasRegularZariskiFrames c i)
    (hT' : HasThomFrames Λ c i') (hR' : HasRegularZariskiFrames c i')
    {k k' : Type u} [Field k] [Field k'] (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    (aX' : X' ⟶ Spec (.of k')) [LocallyOfFiniteType aX'] :
    thomFundamentalClassMap Λ hT' hR' aX' =
      supportedClassMap Λ i' (restrictSupportedClass Λ e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv (leftDerivedUpperStarTateShiftIso Λ e c)
        (thomFundamentalClass Λ hT hR aX)) := by
  rw [restrictSupportedClass_thomFundamentalClass_of_etale Λ e hg hT hR hT' hR' aX aX']
  rfl

end AlgebraicGeometry.Etale
