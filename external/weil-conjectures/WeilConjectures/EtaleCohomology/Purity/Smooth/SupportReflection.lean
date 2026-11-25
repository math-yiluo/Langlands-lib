/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedTensor

/-!
# Reflections into objects supported on a closed subscheme

Let `i : Z ⟶ X` be a closed immersion. An object of `D(X_ét, Λ)` is *supported on `Z`* if it
restricts to zero on the open complement of `Z`. A morphism `γ : K ⟶ T` is a *reflection into
the objects supported on `Z`* (`AlgebraicGeometry.Etale.IsSupportReflection`) if every morphism
from `K` to an object supported on `Z` factors uniquely through `γ`.

The adjoint `Λ_Z ⟶ Ri^! L` of a class `γ : Λ_X ⟶ Ri_! Ri^! L` with supports
(`AlgebraicGeometry.Etale.supportedClassMap`) is an isomorphism if and only if `γ` is such a
reflection (`AlgebraicGeometry.Etale.isIso_supportedClassMap_iff_isSupportReflection`): the
restriction map `Λ_X ⟶ Ri_! Λ_Z` is one, and two reflections differ by an isomorphism. The
notion is intrinsic to `D(X_ét, Λ)`, which makes it convenient to compare classes supported on
different closed immersions with the same range, and to pass to a closed subscheme `Z₁ ⊇ Z`
along the pullback `Li₁^*`, which is fully faithful on the objects supported on `Z₁`
(`AlgebraicGeometry.Etale.IsSupportReflection.of_leftDerivedUpperStar`).

## Main definitions

- `AlgebraicGeometry.Etale.IsSupportReflection`

## Main statements

- `AlgebraicGeometry.Etale.isIso_supportedClassMap_iff_isSupportReflection`
- `AlgebraicGeometry.Etale.IsSupportReflection.isIso_leftDerivedUpperStar_map`
- `AlgebraicGeometry.Etale.IsSupportReflection.of_leftDerivedUpperStar`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Support

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

omit [Finite Λ] in
/-- `Ri_* B` is supported on `Z`. -/
lemma isZero_leftDerivedUpperStar_openComplement_rightDerivedLowerStar
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((R((i)_*[ModuleCat.{u + 1} Λ])).obj B)) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) i
  exact (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint _ i B _
    (disjoint_range_openComplement_ι i)).of_iso
      ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).mapIso (e.app B)).symm

/-- For an object `K` supported on `Z`, the unit `K ⟶ Ri_* Li^* K` is an isomorphism. -/
lemma isIso_unit_app_of_isZero (K : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app K) := by
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion Λ i
  have := isIso_counit_app_of_isZero Λ i K hK
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) i
  let φ : (R((i)_*[ModuleCat.{u + 1} Λ])).obj ((R(i)^![Λ]).obj K) ≅ K :=
    (e.app _).symm ≪≫ asIso ((rightDerivedUpperShriekAdjunction Λ i).counit.app K)
  rw [NatTrans.isIso_app_iff_of_iso _ φ.symm]
  have h := adj.right_triangle_components ((R(i)^![Λ]).obj K)
  have : IsIso (adj.unit.app ((R((i)_*[ModuleCat.{u + 1} Λ])).obj
      ((R(i)^![Λ]).obj K)) ≫ (R((i)_*[ModuleCat.{u + 1} Λ])).map
        (adj.counit.app ((R(i)^![Λ]).obj K))) := by
    rw [h]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ ((R((i)_*[ModuleCat.{u + 1} Λ])).map
    (adj.counit.app ((R(i)^![Λ]).obj K)))

/-- For an object `K` supported on `Z`, the derived pullback `Li^*` is bijective on morphisms with
target `K`. -/
lemma bijective_leftDerivedUpperStar_map_of_isZero
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj K))
    (P : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Function.Bijective (fun f : P ⟶ K ↦ (L((i)^*[ModuleCat.{u + 1} Λ])).map f) := by
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i
  have := isIso_unit_app_of_isZero Λ i K hK
  have : (fun f : P ⟶ K ↦ (L((i)^*[ModuleCat.{u + 1} Λ])).map f) =
      (adj.homEquiv _ _).symm ∘ (fun f ↦ f ≫ adj.unit.app K) := by
    funext f
    rw [Function.comp_apply, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).left_triangle_components K]
    exact (Category.comp_id _).symm
  rw [this]
  exact (Equiv.bijective _).comp (bijective_comp_right_of_isIso _)

/-- Morphisms from an object supported on `Z` to `L` factor uniquely through the counit
`Ri_! Ri^! L ⟶ L`. -/
lemma bijective_comp_counit_of_isZero
    (S : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hS : IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj S))
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Function.Bijective (fun f : S ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L) ↦
      f ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app L) :=
  ⟨fun _ f₂ hf ↦ (existsUnique_comp_counit_of_isZero Λ i i.openComplement.ι
      i.range_eq_compl_range_openComplement_ι hS (f₂ ≫ _)).unique hf rfl,
    fun g ↦ (existsUnique_comp_counit_of_isZero Λ i i.openComplement.ι
      i.range_eq_compl_range_openComplement_ι hS g).exists⟩

end Support

section Reflection

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

variable {Λ} in
/-- A morphism `γ : K ⟶ T` is a *reflection into the objects supported on `Z`* if every morphism
from `K` to an object supported on `Z` (restricting to zero on the open complement of `Z`)
factors uniquely through `γ`. -/
def IsSupportReflection {K T : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : K ⟶ T) : Prop :=
  ∀ S : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj S) →
      Function.Bijective (fun f : T ⟶ S ↦ γ ≫ f)

variable {Λ} {i} {K K' T T' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}

omit [Finite Λ] in
/-- A reflection followed by an isomorphism is a reflection. -/
lemma IsSupportReflection.comp_iso {γ : K ⟶ T} (hγ : IsSupportReflection i γ) (θ : T ≅ T') :
    IsSupportReflection i (γ ≫ θ.hom) := by
  intro S hS
  have : (fun f : T' ⟶ S ↦ (γ ≫ θ.hom) ≫ f) = (fun g ↦ γ ≫ g) ∘ (fun f ↦ θ.hom ≫ f) := by
    funext f
    simp only [Function.comp_apply, Category.assoc]
  rw [this]
  exact (hγ S hS).comp (bijective_iso_hom_comp θ)

omit [Finite Λ] in
/-- If a morphism followed by an isomorphism is a reflection, so is the morphism. -/
lemma IsSupportReflection.of_comp_iso {γ : K ⟶ T} (θ : T ≅ T')
    (hγ : IsSupportReflection i (γ ≫ θ.hom)) : IsSupportReflection i γ := by
  have := hγ.comp_iso θ.symm
  rwa [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] at this

omit [Finite Λ] in
/-- An isomorphism followed by a reflection is a reflection. -/
lemma IsSupportReflection.iso_comp {γ : K ⟶ T} (hγ : IsSupportReflection i γ) (σ : K' ⟶ K)
    [IsIso σ] : IsSupportReflection i (σ ≫ γ) := by
  intro S hS
  have : (fun f : T ⟶ S ↦ (σ ≫ γ) ≫ f) = (fun g ↦ σ ≫ g) ∘ (fun f ↦ γ ≫ f) := by
    funext f
    simp only [Function.comp_apply, Category.assoc]
  rw [this]
  exact (bijective_comp_left_of_isIso σ).comp (hγ S hS)

omit [Finite Λ] in
/-- **Two reflections differ by an isomorphism.** If `γ` and `γ ≫ a` are reflections into the
objects supported on `Z` and the targets of `γ` and `a` are supported on `Z`, then `a` is an
isomorphism. -/
lemma IsSupportReflection.isIso_of_comp {γ : K ⟶ T} {a : T ⟶ T'} (hγ : IsSupportReflection i γ)
    (hγa : IsSupportReflection i (γ ≫ a))
    (hT : IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj T))
    (hT' : IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj T')) : IsIso a := by
  obtain ⟨b, hb⟩ := (hγa T hT).2 γ
  dsimp only at hb
  refine ⟨b, (hγ T hT).1 ?_, (hγa T' hT').1 ?_⟩
  · dsimp only
    rw [← Category.assoc, hb, Category.comp_id]
  · dsimp only
    rw [← Category.assoc, hb, Category.comp_id]

variable (Λ i) in
/-- The restriction map `Λ_X ⟶ Ri_! Λ_Z` is a reflection into the objects supported on `Z`. -/
lemma isSupportReflection_supportedRestrictionMap :
    IsSupportReflection i (supportedRestrictionMap Λ i) := by
  intro S hS
  have := isIso_counit_app_of_isZero Λ i S hS
  exact bijective_comp_of_iso _
    (asIso ((rightDerivedUpperShriekAdjunction Λ i).counit.app S)).symm
    (bijective_supportedRestrictionMap_comp Λ i _)

variable (Λ) in
/-- **Adjoints of classes with supports and reflections.** The adjoint `Λ_Z ⟶ Ri^! L` of a class
`γ : Λ_X ⟶ Ri_! Ri^! L` (`AlgebraicGeometry.Etale.supportedClassMap`) is an isomorphism if and
only if `γ` is a reflection into the objects supported on `Z`. -/
theorem isIso_supportedClassMap_iff_isSupportReflection
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    IsIso (supportedClassMap Λ i γ) ↔ IsSupportReflection i γ := by
  have hγ := supportedRestrictionMap_comp_map_supportedTranspose Λ i γ
  rw [← supportedClassMap_eq_supportedTranspose] at hγ
  constructor
  · intro h
    have := (isSupportReflection_supportedRestrictionMap Λ i).comp_iso
      ((R(i)_![ModuleCat.{u + 1} Λ]).mapIso (asIso (supportedClassMap Λ i γ)))
    rwa [Functor.mapIso_hom, asIso_hom, hγ] at this
  · intro h
    have : IsIso ((R(i)_![ModuleCat.{u + 1} Λ]).map (supportedClassMap Λ i γ)) :=
      (isSupportReflection_supportedRestrictionMap Λ i).isIso_of_comp (by rwa [hγ])
        (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint _ i _ _
          (disjoint_range_openComplement_ι i))
        (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint _ i _ _
          (disjoint_range_openComplement_ι i))
    exact isIso_of_reflects_iso _ (R(i)_![ModuleCat.{u + 1} Λ])

variable (Λ i) in
/-- The unit `K ⟶ Ri_* Li^* K` is a reflection into the objects supported on `Z`. -/
lemma isSupportReflection_unit (K : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) :
    IsSupportReflection i ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app
      K) := by
  intro S hS
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion Λ i
  have : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map (adj.unit.app K)) := by
    have h := adj.left_triangle_components K
    have : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map (adj.unit.app K) ≫
        adj.counit.app ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K))
  have hF := bijective_leftDerivedUpperStar_map_of_isZero Λ i S hS
  have key : (fun f : K ⟶ S ↦ (L((i)^*[ModuleCat.{u + 1} Λ])).map f) ∘
      (fun f ↦ adj.unit.app K ≫ f) =
      (fun g ↦ (L((i)^*[ModuleCat.{u + 1} Λ])).map (adj.unit.app K) ≫ g) ∘
        (fun f ↦ (L((i)^*[ModuleCat.{u + 1} Λ])).map f) := by
    funext f
    simp only [Function.comp_apply, Functor.map_comp]
  exact ((hF K).of_comp_iff' _).1 (by
    rw [key]
    exact (bijective_comp_left_of_isIso _).comp (hF _))

/-- The derived pullback `Li^*` of a reflection into the objects supported on `Z`, with target
supported on `Z`, is an isomorphism. -/
lemma IsSupportReflection.isIso_leftDerivedUpperStar_map {γ : K ⟶ T}
    (hγ : IsSupportReflection i γ)
    (hT : IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj T)) :
    IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map γ) := by
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i
  obtain ⟨θ, hθ⟩ := (isSupportReflection_unit Λ i K T hT).2 γ
  dsimp only at hθ
  have : IsIso θ := (isSupportReflection_unit Λ i K).isIso_of_comp (by rwa [hθ])
    (isZero_leftDerivedUpperStar_openComplement_rightDerivedLowerStar Λ i _) hT
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion Λ i
  have : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map (adj.unit.app K)) := by
    have h := adj.left_triangle_components K
    have : IsIso ((L((i)^*[ModuleCat.{u + 1} Λ])).map (adj.unit.app K) ≫
        adj.counit.app ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K))
  rw [← hθ, Functor.map_comp]
  infer_instance

/-- **Reflections and restriction to a closed subscheme.** Let `Z ⊆ Z₁` be closed in `X`, with
`i₁ : Z₁ ⟶ X`, and let `j : Z' ⟶ Z₁` be a closed immersion whose open complement maps into the
open complement of `Z`. If the restriction `K' ≅ Li₁^* K ⟶ Li₁^* T` of `γ : K ⟶ T` is a
reflection into the objects of `D(Z₁)` supported on `Z'`, then `γ` is a reflection into the
objects of `D(X)` supported on `Z`. Indeed `Li₁^*` is bijective on morphisms into objects
supported on `Z₁`, and carries objects supported on `Z` to objects supported on `Z'`. -/
theorem IsSupportReflection.of_leftDerivedUpperStar {Z₁ Z' : Scheme.{u}} (i₁ : Z₁ ⟶ X)
    (j : Z' ⟶ Z₁) [IsClosedImmersion i₁] [IsClosedImmersion j]
    (hsub : Set.range i.base ⊆ Set.range i₁.base)
    (hd : Disjoint (Set.range (j.openComplement.ι ≫ i₁).base) (Set.range i.base))
    {K' : DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {γ : K ⟶ T}
    (σ : K' ⟶ (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj K) [IsIso σ]
    (h : IsSupportReflection j (σ ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map γ)) :
    IsSupportReflection i γ := by
  intro S hS
  have hS₁ : IsZero ((L((i₁.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj S) := by
    have hr : Set.range i₁.openComplement.ι.base ⊆ Set.range i.openComplement.ι.base := by
      rw [Scheme.Hom.range_openComplement_ι, Scheme.Hom.range_openComplement_ι]
      exact Set.compl_subset_compl.2 hsub
    rw [← IsOpenImmersion.lift_fac i.openComplement.ι i₁.openComplement.ι hr]
    exact isZero_leftDerivedUpperStar_comp_of_isZero _ i.openComplement.ι hS _
  have hS' : IsZero ((L((j.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((L((i₁)^*[ModuleCat.{u + 1} Λ])).obj S)) := by
    have hr : Set.range (j.openComplement.ι ≫ i₁).base ⊆ Set.range i.openComplement.ι.base := by
      rw [Scheme.Hom.range_openComplement_ι]
      exact hd.subset_compl_right
    refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp _ j.openComplement.ι i₁).app S).symm
    rw [← IsOpenImmersion.lift_fac i.openComplement.ι _ hr]
    exact isZero_leftDerivedUpperStar_comp_of_isZero _ i.openComplement.ι hS _
  have hF := bijective_leftDerivedUpperStar_map_of_isZero Λ i₁ S hS₁
  have key : ((fun g ↦ σ ≫ g) ∘ (fun f : K ⟶ S ↦ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map f)) ∘
      (fun f : T ⟶ S ↦ γ ≫ f) =
      (fun g ↦ (σ ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map γ) ≫ g) ∘
        (fun f : T ⟶ S ↦ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map f) := by
    funext f
    simp only [Function.comp_apply, Functor.map_comp, Category.assoc]
  exact (((bijective_comp_left_of_isIso σ).comp (hF K)).of_comp_iff' _).1 (by
    rw [key]
    exact (h _ hS').comp (hF T))

end Reflection

end Etale

end AlgebraicGeometry
