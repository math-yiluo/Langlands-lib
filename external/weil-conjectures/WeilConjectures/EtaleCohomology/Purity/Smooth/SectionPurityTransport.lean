/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomFundamentalClassTransport
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientation

/-!
# Transport of the purity map and of the purity of a section along an étale base change

Let `i : Z ⟶ X` be a closed immersion with Thom frames and `i' : Z' ⟶ X'` its base change along
an étale morphism `e : X' ⟶ X` (for instance an isomorphism), `g : Z' ⟶ Z`. The purity map
`cl_{i'} : Λ_{Z'} ⟶ Ri'^!(Λ_{X'}(c)[2c])` (`AlgebraicGeometry.Etale.thomFundamentalClassMap`) is
the pullback `Lg^* cl_i` followed by the exceptional base change
`Lg^* Ri^! ⟶ Ri'^! Le^*` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`), through
`Λ_{Z'} ≅ Lg^* Λ_Z` and `Le^*(Λ_X(c)[2c]) ≅ Λ_{X'}(c)[2c]`
(`AlgebraicGeometry.Etale.thomFundamentalClassMap_baseChange_of_etale`): the fundamental class
restricts to the fundamental class
(`AlgebraicGeometry.Etale.restrictSupportedClass_thomFundamentalClass_of_etale`) and the adjoint of
a restricted class with supports is the base change of its adjoint
(`AlgebraicGeometry.Etale.supportedClassMap_restrictSupportedClass`).

For a closed section `s` of a smooth morphism `g : V ⟶ B` and its base change `s'` along an
étale `V' ⟶ V`, the purity isomorphisms `Rs^!(Λ_V(c)[2c]) ≅ Λ_B`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekTateObjectIsoOfSection`, the inverses of the
purity maps) correspond under the exceptional base change
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekTateObjectIsoOfSection_baseChange`). This is the
geometric form of the coefficient-change statement
`SupportedCoefficientChange.map_rightDerivedUpperShriekTateObjectIsoOfSection`,
a step of the base change compatibility of the canonical orientation along an isomorphism of
pairs (blueprint `proposition-compatibility-purity-base-change`, the Frobenius square).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section ClosedImmersion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ]
  {X X' Z Z' : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ X'] {c : ℕ}
  {i : Z ⟶ X} {i' : Z' ⟶ X'} [IsClosedImmersion i] [IsClosedImmersion i']
  (e : X' ⟶ X) [AlgebraicGeometry.Etale e] {g : Z' ⟶ Z} (hg : IsPullback g i' i e)

/-- **The purity map is compatible with étale base change.** For `i' : Z' ⟶ X'` the base change
of `i : Z ⟶ X` along an étale `e : X' ⟶ X`, the pullback `Lg^* cl_i` of the purity map of `i`,
followed by the exceptional base change `Lg^* Ri^! ⟶ Ri'^! Le^*` at `Λ_X(c)[2c]` and
`Ri'^!(Le^*(Λ_X(c)[2c]) ≅ Λ_{X'}(c)[2c])`, is `Λ_{Z'} ≅ Lg^* Λ_Z` followed by the purity map of
`i'`. -/
theorem thomFundamentalClassMap_baseChange_of_etale
    (hT : HasThomFrames Λ c i) (hR : HasRegularZariskiFrames c i)
    (hT' : HasThomFrames Λ c i') (hR' : HasRegularZariskiFrames c i')
    {k k' : Type u} [Field k] [Field k'] (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    (aX' : X' ⟶ Spec (.of k')) [LocallyOfFiniteType aX'] :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map (thomFundamentalClassMap Λ hT hR aX) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ hg).app ((tateObject Λ X c)⟦2 * (c : ℤ)⟧) ≫
          (R(i')^![Λ]).map (leftDerivedUpperStarTateShiftIso Λ e c).hom =
      (leftDerivedUpperStarConstantComplexIso Λ g).hom ≫
        thomFundamentalClassMap Λ hT' hR' aX' := by
  rw [thomFundamentalClassMap_eq_supportedClassMap_restrictSupportedClass Λ e hg hT hR hT' hR'
    aX aX', supportedClassMap_restrictSupportedClass, Iso.hom_inv_id_assoc,
    thomFundamentalClassMap]

end ClosedImmersion

section Section

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ]
  {V B V' B' : Scheme.{u}} (c : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension c g] (s : B ⟶ V)
  [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) (g' : V' ⟶ B') [SmoothOfRelativeDimension c g']
  (s' : B' ⟶ V') [IsClosedImmersion s'] (hs' : s' ≫ g' = 𝟙 B')
  (eV : V' ⟶ V) [AlgebraicGeometry.Etale eV] {eB : B' ⟶ B} (hsq : IsPullback eB s' s eV)
  {k k' : Type u} [Field k] [Field k'] (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
  [LocallyOfFiniteType aB] (aB' : B' ⟶ Spec (.of k')) [IsSeparated aB']
  [LocallyOfFiniteType aB'] [HasInvertibleExponent Λ V] [HasInvertibleExponent Λ V']

/-- **Purity for a section of a smooth morphism is compatible with étale base change.** For
`g : V ⟶ B` smooth of relative dimension `c` with a closed section `s`, and `s'` the base change
of `s` along an étale `eV : V' ⟶ V` (a section of `g'`), the purity isomorphisms
`Rs^!(Λ_V(c)[2c]) ≅ Λ_B` and `Rs'^!(Λ_{V'}(c)[2c]) ≅ Λ_{B'}`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekTateObjectIsoOfSection`) correspond under the
exceptional base change `LeB^* Rs^! ⟶ Rs'^! LeV^*`, `LeV^*(Λ_V(c)[2c]) ≅ Λ_{V'}(c)[2c]` and
`LeB^* Λ_B ≅ Λ_{B'}`. -/
theorem rightDerivedUpperShriekTateObjectIsoOfSection_baseChange :
    (L((eB)^*[ModuleCat.{u + 1} Λ])).map
        (rightDerivedUpperShriekTateObjectIsoOfSection Λ c g s hs aB).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ eB).hom =
      ((rightDerivedUpperShriekBaseChangeMap Λ hsq).app ((tateObject Λ V c)⟦2 * (c : ℤ)⟧) ≫
          (R(s')^![Λ]).map (leftDerivedUpperStarTateShiftIso Λ eV c).hom) ≫
        (rightDerivedUpperShriekTateObjectIsoOfSection Λ c g' s' hs' aB').hom := by
  have := SmoothOfRelativeDimension.smooth c g
  have := SmoothOfRelativeDimension.smooth c g'
  have h := thomFundamentalClassMap_baseChange_of_etale Λ eV hsq
    (hasThomFrames_of_section Λ c g s hs aB)
    (hasRegularZariskiFrames_of_section c g s hs) (hasThomFrames_of_section Λ c g' s' hs' aB')
    (hasRegularZariskiFrames_of_section c g' s' hs') (g ≫ aB) (g' ≫ aB')
  have := isIso_thomFundamentalClassMap Λ (hasThomFrames_of_section Λ c g s hs aB)
    (hasRegularZariskiFrames_of_section c g s hs) (g ≫ aB)
  have := isIso_thomFundamentalClassMap Λ (hasThomFrames_of_section Λ c g' s' hs' aB')
    (hasRegularZariskiFrames_of_section c g' s' hs') (g' ≫ aB')
  simp only [rightDerivedUpperShriekTateObjectIsoOfSection, Iso.symm_hom, asIso_inv]
  rw [← cancel_epi ((L((eB)^*[ModuleCat.{u + 1} Λ])).map (thomFundamentalClassMap Λ
      (hasThomFrames_of_section Λ c g s hs aB) (hasRegularZariskiFrames_of_section c g s hs)
      (g ≫ aB))), ← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.assoc, reassoc_of% h, IsIso.hom_inv_id, Category.comp_id]

end Section

end AlgebraicGeometry.Etale
