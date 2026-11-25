/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange

/-!
# Restriction of classes with supports and base change of the exceptional inverse image

Auxiliary statements on classes with supports used for the cohomology of the projective line
(`AlgebraicGeometry.Etale.isIso_projectiveLineDecompositionMap`).

* The restriction of supports `Le^* Ri_! Ri^! L ⟶ Ri'_! Ri'^! L'` is the compact-support base
  change followed by the base change map of the exceptional inverse image
  (`AlgebraicGeometry.Etale.supportedRestriction_eq`).
* Up to an isomorphism of `Λ_{Z'}` which does not depend on the class, the adjoint of a
  restricted class is the base change map of the exceptional inverse image applied to the
  pullback of the adjoint of the class
  (`AlgebraicGeometry.Etale.exists_isIso_supportedClassMap_restrictSupportedClass`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

section Restriction

variable {U X Z Z' : Scheme.{u}} (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U) [IsClosedImmersion i]
  [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)

variable (Λ) in
/-- **The restriction of supports is a base change map**: the restriction of supports
`Le^* Ri_! Ri^! L ⟶ Ri'_! Ri'^! L'` along `e` (`AlgebraicGeometry.Etale.supportedRestriction`)
is the compact-support base change `Le^* Ri_! ⟶ Ri'_! Lg^*` followed by `Ri'_!` of the base
change map `Lg^* Ri^! ⟶ Ri'^! Le^*` of the exceptional inverse image and of `τ`. -/
lemma supportedRestriction_eq
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') :
    supportedRestriction Λ e i i' g hg L L' τ =
      (rightDerivedLowerShriekBaseChangeMap Λ hg).app ((R(i)^![Λ]).obj L) ≫
        (R(i')_![ModuleCat.{u + 1} Λ]).map
          ((rightDerivedUpperShriekBaseChangeMap Λ hg).app L ≫ (R(i')^![Λ]).map τ.hom) := by
  refine (existsUnique_supportedRestriction Λ e i i' g hg L L' τ).unique
    (existsUnique_supportedRestriction Λ e i i' g hg L L' τ).exists.choose_spec ?_
  have hc := (rightDerivedUpperShriekAdjunction Λ i').counit.naturality τ.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ hg
  have hm :
      (R(i')_![ModuleCat.{u + 1} Λ]).map ((rightDerivedUpperShriekBaseChangeMap Λ hg).app L) ≫
      (rightDerivedUpperShriekAdjunction _ i').counit.app _ =
      (inv (rightDerivedLowerShriekBaseChangeMap Λ hg)).app ((R(i)^![Λ]).obj L) ≫
        L((e)^*[ModuleCat.{u + 1} Λ]).map ((rightDerivedUpperShriekAdjunction _ i).counit.app L) :=
    mateEquiv_counit _ _ _ L
  rw [Functor.map_comp, Category.assoc, Category.assoc, hc, reassoc_of% hm]
  rw [← NatTrans.comp_app_assoc, IsIso.hom_inv_id, NatTrans.id_app, Category.id_comp]

variable (Λ) in
include hg in
/-- **The adjoint of a restricted class.** For the base change `i' : Z' ⟶ U`, `g : Z' ⟶ Z` of a
closed immersion `i : Z ⟶ X` along `e : U ⟶ X`, there is an isomorphism
`Θ : Λ_{Z'} ≅ Lg^* Λ_Z` such that for every class `γ : Λ_X ⟶ Ri_! Ri^! L` with supports, the
adjoint of its restriction along `e` (`AlgebraicGeometry.Etale.restrictSupportedClass`) is

`Λ_{Z'} ≅ Lg^* Λ_Z ⟶ Lg^* Ri^! L ⟶ Ri'^! Le^* L ≅ Ri'^! L'`,

the pullback of the adjoint of `γ` followed by the base change map of the exceptional inverse
image (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`). The isomorphism `Θ`
compares two reflections of `Λ_U` into the objects of the form `Ri'_! N`. -/
theorem exists_isIso_supportedClassMap_restrictSupportedClass :
    ∃ Θ : constantComplex Λ Z' ⟶ (L((g)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Z),
      IsIso Θ ∧ ∀ (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
        (L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
        (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L')
        (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)),
        supportedClassMap Λ i' (restrictSupportedClass Λ e i i' g hg
            (leftDerivedUpperStarConstantComplexIso Λ e).inv τ γ) =
          Θ ≫ (L((g)^*[ModuleCat.{u + 1} Λ])).map (supportedClassMap Λ i γ) ≫
            (rightDerivedUpperShriekBaseChangeMap Λ hg).app L ≫ (R(i')^![Λ]).map τ.hom := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ hg
  set v := (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
    (L((e)^*[ModuleCat.{u + 1} Λ])).map (supportedRestrictionMap Λ i) ≫
      (rightDerivedLowerShriekBaseChangeMap Λ hg).app (constantComplex Λ Z) with hv_def
  set u' := supportedRestrictionMap Λ i'
  have hv (N : DerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      Function.Bijective (fun f : (R(i')_![ModuleCat.{u + 1} Λ]).obj
          ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Z)) ⟶
            (R(i')_![ModuleCat.{u + 1} Λ]).obj N ↦ v ≫ f) := by
    have h := (bijective_leftDerivedUpperStar_map_supportedRestrictionMap_comp Λ e i i' g hg
      N).comp (bijective_comp_left_of_isIso
        ((rightDerivedLowerShriekBaseChangeMap Λ hg).app (constantComplex Λ Z)))
    convert h using 1
    funext f
    simp [v]
  refine ⟨supportedTranspose Λ i' v, ?_, ?_⟩
  · have hΘ : u' ≫ (R(i')_![ModuleCat.{u + 1} Λ]).map (supportedTranspose Λ i' v) = v :=
      supportedRestrictionMap_comp_map_supportedTranspose Λ i' v
    obtain ⟨k, hk⟩ := (hv _).2 u'
    dsimp only at hk
    have h₁ : (R(i')_![ModuleCat.{u + 1} Λ]).map (supportedTranspose Λ i' v) ≫ k = 𝟙 _ :=
      (bijective_supportedRestrictionMap_comp Λ i' _).1 (by
        dsimp only
        rw [← Category.assoc, hΘ, hk, Category.comp_id])
    have h₂ : k ≫ (R(i')_![ModuleCat.{u + 1} Λ]).map (supportedTranspose Λ i' v) = 𝟙 _ :=
      (hv _).1 (by
        dsimp only
        rw [← Category.assoc, hk, hΘ]
        exact (Category.comp_id v).symm)
    have : IsIso ((R(i')_![ModuleCat.{u + 1} Λ]).map (supportedTranspose Λ i' v)) :=
      ⟨k, h₁, h₂⟩
    exact isIso_of_reflects_iso _ (R(i')_![ModuleCat.{u + 1} Λ])
  · intro L L' τ γ
    have hγ : supportedRestrictionMap Λ i ≫
        (R(i)_![ModuleCat.{u + 1} Λ]).map (supportedClassMap Λ i γ) = γ :=
      supportedRestrictionMap_comp_map_supportedTranspose Λ i γ
    rw [supportedClassMap_eq_supportedTranspose, ← supportedTranspose_comp]
    congr 1
    conv_lhs => rw [restrictSupportedClass, supportedRestriction_eq, ← hγ]
    have hnat := (rightDerivedLowerShriekBaseChangeMap Λ hg).naturality (supportedClassMap Λ i γ)
    dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
    simp only [v, Functor.map_comp, Category.assoc, reassoc_of% hnat]

variable (Λ) in
include hg in
/-- If the adjoints of two classes with supports differ by an automorphism of `Λ_Z`, then the
adjoint of the restriction of the first one is an isomorphism if and only if the adjoint of
the restriction of the second one is. -/
theorem isIso_supportedClassMap_restrictSupportedClass_iff_of_eq
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L')
    (γ₁ γ₂ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))
    (θ : constantComplex Λ Z ⟶ constantComplex Λ Z) [IsIso θ]
    (h : supportedClassMap Λ i γ₁ = θ ≫ supportedClassMap Λ i γ₂) :
    IsIso (supportedClassMap Λ i' (restrictSupportedClass Λ e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv τ γ₁)) ↔
      IsIso (supportedClassMap Λ i' (restrictSupportedClass Λ e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv τ γ₂)) := by
  obtain ⟨Θ, hΘ, hΘ'⟩ := exists_isIso_supportedClassMap_restrictSupportedClass Λ e i i' g hg
  rw [hΘ' L L' τ γ₁, hΘ' L L' τ γ₂, h]
  simp only [Functor.map_comp, Category.assoc, isIso_comp_left_iff]

end Restriction

end Etale

end AlgebraicGeometry
