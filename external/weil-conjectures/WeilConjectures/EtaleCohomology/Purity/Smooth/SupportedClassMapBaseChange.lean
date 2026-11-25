/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomologySupports
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomologyGysin
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLowerStarExchange

/-!
# The adjoint of a restricted class with supports

For the base change `i' : Z' ⟶ U`, `g : Z' ⟶ Z` of a closed immersion `i : Z ⟶ X` along
`e : U ⟶ X`, the adjoint `Λ_{Z'} ⟶ Ri'^! L'` of the restriction along `e` of a class
`γ : Λ_X ⟶ Ri_! Ri^! L` with supports is

`Λ_{Z'} ≅ Lg^* Λ_Z ⟶ Lg^* Ri^! L ⟶ Ri'^! Le^* L ≅ Ri'^! L'`,

the pullback of the adjoint of `γ`, read through the canonical identification
`Lg^* Λ_Z ≅ Λ_{Z'}`, followed by the base change map of the exceptional inverse image
(`AlgebraicGeometry.Etale.supportedClassMap_restrictSupportedClass`). This makes
`AlgebraicGeometry.Etale.exists_isIso_supportedClassMap_restrictSupportedClass` explicit: the
isomorphism `Θ` there is the canonical one. The proof uses that `Ri_! ≅ Ri_*` intertwines the
exchange maps (`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_comp_lowerStarIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

section Unit

variable {X S X' S' : Scheme.{u}} {q : X ⟶ S} {x : S' ⟶ S} {q' : X' ⟶ S'} {g' : X' ⟶ X}

omit [Finite Λ] in
/-- **Base change of an adjoint morphism.** For a commutative square `g' ≫ q = q' ≫ x`, the
pullback along `x` of `η_P ≫ Rq_* c : P ⟶ Rq_* K`, followed by the base change map
`Lx^* Rq_* ⟶ Rq'_* Lg'^*`, is the adjoint of `Lq'^* Lx^* P ≅ Lg'^* Lq^* P ⟶ Lg'^* K`. -/
@[reassoc]
lemma leftDerivedUpperStar_map_unit_comp_map_comp_derivedBaseChangeMap (sq : CommSq g' q' q x)
    {P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (c : (L((q)^*[ModuleCat.{u + 1} Λ])).obj P ⟶ K) :
    (L((x)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app P ≫
          (R((q)_*[ModuleCat.{u + 1} Λ])).map c) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q').unit.app
          ((L((x)^*[ModuleCat.{u + 1} Λ])).obj P) ≫
        (R((q')_*[ModuleCat.{u + 1} Λ])).map
          ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app P ≫
            (L((g')^*[ModuleCat.{u + 1} Λ])).map c) := by
  have hn := (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).naturality c
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc,
    map_unit_derivedBaseChangeMap_app (ModuleCat.{u + 1} Λ) sq P, Functor.map_comp,
    Category.assoc]

omit [Finite Λ] in
/-- **Base change of an adjoint morphism, with identifications.** For a commutative square
`g' ≫ q = q' ≫ x`, identifications `σ : Lx^* P ⟶ P'` and `τ : Lg'^* K ⟶ K'` and morphisms
`c : Lq^* P ⟶ K`, `c' : Lq'^* P' ⟶ K'` compatible with them, the pullback along `x` of
`η_P ≫ Rq_* c`, followed by the base change map and `Rq'_* τ`, is `σ ≫ η_{P'} ≫ Rq'_* c'`. -/
lemma leftDerivedUpperStar_map_unit_comp_map_comp_derivedBaseChangeMap_comp
    (sq : CommSq g' q' q x)
    {P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {P' : DerivedCategory (Sheaf S'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (c : (L((q)^*[ModuleCat.{u + 1} Λ])).obj P ⟶ K)
    (c' : (L((q')^*[ModuleCat.{u + 1} Λ])).obj P' ⟶ K')
    (σ : (L((x)^*[ModuleCat.{u + 1} Λ])).obj P ⟶ P')
    (τ : (L((g')^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K')
    (h : (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app P ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map c ≫ τ =
      (L((q')^*[ModuleCat.{u + 1} Λ])).map σ ≫ c') :
    (L((x)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app P ≫
          (R((q)_*[ModuleCat.{u + 1} Λ])).map c) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K ≫
          (R((q')_*[ModuleCat.{u + 1} Λ])).map τ =
      σ ≫ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q').unit.app P' ≫
        (R((q')_*[ModuleCat.{u + 1} Λ])).map c' := by
  rw [leftDerivedUpperStar_map_unit_comp_map_comp_derivedBaseChangeMap_assoc (Λ := Λ) sq c,
    ← Functor.map_comp, Category.assoc, h, Functor.map_comp, Adjunction.unit_naturality_assoc]

end Unit

section Restriction

variable {U X Z Z' : Scheme.{u}} (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U) [IsClosedImmersion i]
  [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)

variable (Λ) in
/-- The restriction map `Λ_X ⟶ Ri_! Λ_Z` (`AlgebraicGeometry.Etale.supportedRestrictionMap`) is
compatible with base change: pulled back along `e` and followed by the compactly supported base
change map `Le^* Ri_! ⟶ Ri'_! Lg^*`, it is the restriction map of `i'` followed by
`Λ_{Z'} ≅ Lg^* Λ_Z`. -/
lemma supportedRestrictionMap_baseChange :
    (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
        (L((e)^*[ModuleCat.{u + 1} Λ])).map (supportedRestrictionMap Λ i) ≫
          (rightDerivedLowerShriekBaseChangeMap Λ hg).app (constantComplex Λ Z) =
      supportedRestrictionMap Λ i' ≫
        (R(i')_![ModuleCat.{u + 1} Λ]).map (leftDerivedUpperStarConstantComplexIso Λ g).inv := by
  have h₁ : supportedRestrictionMap Λ i =
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app _ ≫
        (R((i)_*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ i).hom) ≫
          (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).inv.app _ := by
    have h := unit_comp_map_comp_inv_eq_supportedRestrictionMap_comp Λ i (𝟙 _)
    simp only [Category.comp_id, CategoryTheory.Functor.map_id, Category.assoc] at h ⊢
    exact h.symm
  have h₂ := leftDerivedUpperStar_map_unit_comp_map_comp_derivedBaseChangeMap (Λ := Λ)
    hg.toCommSq (P := constantComplex Λ X) (leftDerivedUpperStarConstantComplexIso Λ i).hom
  have hsq : (L((i')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) hg.toCommSq).hom.app (constantComplex Λ X) ≫
        (L((g)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ i).hom =
      (leftDerivedUpperStarConstantComplexIso Λ i').hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ g).inv := by
    rw [← cancel_mono (leftDerivedUpperStarConstantComplexIso Λ g).hom, Category.assoc,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact leftDerivedUpperStarConstantComplexIso_square Λ hg.toCommSq
  rw [← unit_comp_map_comp_inv_eq_supportedRestrictionMap_comp Λ i'
      (leftDerivedUpperStarConstantComplexIso Λ g).inv, h₁, Functor.map_comp, Category.assoc,
    leftDerivedUpperStar_map_lowerStarIso_inv_comp_rightDerivedLowerShriekBaseChangeMap,
    reassoc_of% h₂, ← Adjunction.unit_naturality_assoc, ← Functor.map_comp_assoc, hsq]

variable (Λ) in
/-- **The adjoint of a restricted class with supports.** The adjoint of the restriction along
`e` of a class `γ : Λ_X ⟶ Ri_! Ri^! L` with supports
(`AlgebraicGeometry.Etale.restrictSupportedClass`) is

`Λ_{Z'} ≅ Lg^* Λ_Z ⟶ Lg^* Ri^! L ⟶ Ri'^! Le^* L ≅ Ri'^! L'`,

the pullback of the adjoint of `γ` followed by the base change map of the exceptional inverse
image (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`). -/
theorem supportedClassMap_restrictSupportedClass
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L')
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    supportedClassMap Λ i' (restrictSupportedClass Λ e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv τ γ) =
      (leftDerivedUpperStarConstantComplexIso Λ g).inv ≫
        (L((g)^*[ModuleCat.{u + 1} Λ])).map (supportedClassMap Λ i γ) ≫
          (rightDerivedUpperShriekBaseChangeMap Λ hg).app L ≫ (R(i')^![Λ]).map τ.hom := by
  have hγ : supportedRestrictionMap Λ i ≫
      (R(i)_![ModuleCat.{u + 1} Λ]).map (supportedClassMap Λ i γ) = γ :=
    supportedRestrictionMap_comp_map_supportedTranspose Λ i γ
  have hnat := (rightDerivedLowerShriekBaseChangeMap Λ hg).naturality (supportedClassMap Λ i γ)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  conv_lhs => rw [restrictSupportedClass, supportedRestriction_eq, ← hγ]
  rw [Functor.map_comp, Category.assoc, reassoc_of% hnat,
    reassoc_of% supportedRestrictionMap_baseChange,
    ← Functor.map_comp_assoc, ← Functor.map_comp, supportedClassMap_eq_supportedTranspose,
    supportedTranspose_comp, supportedTranspose_supportedRestrictionMap, Category.id_comp]
  simp only [Category.assoc]


end Restriction

section OpenImmersion

variable {Z V X : Scheme.{u}} (i : Z ⟶ V) (j : V ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
  [IsClosedImmersion (i ≫ j)]

variable (Λ) in
/-- **Classes supported in an open are determined by their restriction to it.** For a closed
immersion `i : Z ⟶ V`, an open immersion `j : V ⟶ X` with `i ≫ j` a closed immersion, two classes
with supports in `Z` whose restrictions along `j` agree are equal. -/
theorem restrictSupportedClass_injective_of_isOpenImmersion
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L' : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (τ : (L((j)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L')
    {γ₁ γ₂ : constantComplex Λ X ⟶
      (R(i ≫ j)_![ModuleCat.{u + 1} Λ]).obj ((R(i ≫ j)^![Λ]).obj L)}
    (h : restrictSupportedClass Λ j (i ≫ j) i (𝟙 Z) (isPullback_id_comp_of_mono i j)
        (leftDerivedUpperStarConstantComplexIso Λ j).inv τ γ₁ =
      restrictSupportedClass Λ j (i ≫ j) i (𝟙 Z) (isPullback_id_comp_of_mono i j)
        (leftDerivedUpperStarConstantComplexIso Λ j).inv τ γ₂) :
    γ₁ = γ₂ := by
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion Λ
    (isPullback_id_comp_of_mono i j)
  apply (supportedClassMap_bijective Λ (i ≫ j) L).injective
  have h' := congrArg (supportedClassMap Λ i) h
  have e : (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_id_comp_of_mono i j)).app L ≫
      (R(i)^![Λ]).map τ.hom = ((asIso (rightDerivedUpperShriekBaseChangeMap Λ
        (isPullback_id_comp_of_mono i j))).app L ≪≫ (R(i)^![Λ]).mapIso τ).hom := rfl
  rw [supportedClassMap_restrictSupportedClass, supportedClassMap_restrictSupportedClass,
    cancel_epi, e, cancel_mono] at h'
  rw [← Functor.id_map (supportedClassMap Λ (i ≫ j) γ₁),
    ← Functor.id_map (supportedClassMap Λ (i ≫ j) γ₂),
    ← NatIso.naturality_1 (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Z),
    ← NatIso.naturality_1 (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Z), h']

end OpenImmersion

section Identity

omit [Finite Λ] in
variable (Λ) in
/-- The identification `L(𝟙 X)^* Λ_X ≅ Λ_X` of the constant complexes is the identity
isomorphism `L(𝟙 X)^* ≅ 𝟭`. -/
lemma leftDerivedUpperStarConstantComplexIso_id_hom (X : Scheme.{u}) :
    (leftDerivedUpperStarConstantComplexIso Λ (𝟙 X)).hom =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app (constantComplex Λ X) := by
  have h := congrArg Iso.hom (leftDerivedUpperStarConstantComplexIso_comp Λ (𝟙 X) (𝟙 X) (𝟙 X)
    (Category.id_comp _).symm)
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h
  have hu := leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} Λ) (𝟙 X)
    (constantComplex Λ X)
  have h₁ : (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.id_comp _).symm).hom.app (constantComplex Λ X) ≫
        (L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).map
          (leftDerivedUpperStarConstantComplexIso Λ (𝟙 X)).hom = 𝟙 _ := by
    rw [← cancel_mono (leftDerivedUpperStarConstantComplexIso Λ (𝟙 X)).hom, Category.assoc,
      ← h, Category.id_comp]
  have h₂ : (L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).map
      (leftDerivedUpperStarConstantComplexIso Λ (𝟙 X)).hom =
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app _ := by
    rw [← cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.id_comp _).symm).hom.app (constantComplex Λ X)), h₁, hu]
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.naturality
    (leftDerivedUpperStarConstantComplexIso Λ (𝟙 X)).hom
  rw [Functor.id_map, h₂, cancel_epi] at hn
  exact hn.symm

omit [Finite Λ] in
variable (Λ) in
/-- `AlgebraicGeometry.Etale.leftDerivedUpperStarConstantComplexIso_id_hom`, in the form
`(L(𝟙 X)^* Λ_X ≅ Λ_X)⁻¹ ≫ (L(𝟙 X)^* ≅ 𝟭) = 𝟙`. -/
@[reassoc]
lemma leftDerivedUpperStarConstantComplexIso_inv_comp_leftDerivedUpperStarId_hom_app
    (X : Scheme.{u}) :
    (leftDerivedUpperStarConstantComplexIso Λ (𝟙 X)).inv ≫
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app (constantComplex Λ X) = 𝟙 _ := by
  rw [← leftDerivedUpperStarConstantComplexIso_id_hom, Iso.inv_hom_id]

end Identity

end Etale

end AlgebraicGeometry
