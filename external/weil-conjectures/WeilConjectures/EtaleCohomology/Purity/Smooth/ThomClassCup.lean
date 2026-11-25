/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportReflection

/-!
# The adjoint of a cup product of classes with supports

Let `i₁ : Z₁ ⟶ U` and `i₂ : Z₂ ⟶ U` be closed immersions, `i : Z ⟶ U` a closed immersion onto
`Z₁ ∩ Z₂`, and `j : Z' ⟶ Z₁` the base change of `i₂` along `i₁`. Let
`α : Λ_U ⟶ Ri₁_! Ri₁^! M` and `β : Λ_U ⟶ Ri₂_! Ri₂^! N` be classes with supports, `N`
invertible. If the adjoint of `α` is an isomorphism (`α` is a fundamental class of `Z₁`) and the
adjoint of the restriction `β|_{Z₁}` of `β` to `Z₁` is an isomorphism, then the adjoint of the cup
product `α ∪ β` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_cupWithSupports`).
This is the inductive step of the model computation `proposition-purity-vector-bundles` (i): the
Thom class of `𝔸^{c+1}_B = 𝔸¹_{𝔸^c_B}` is the cup product of the Kummer boundary of the coordinate
of the affine line and the pullback of the Thom class of `𝔸^c_B`.

The proof uses the language of reflections into objects with supports
(`AlgebraicGeometry.Etale.IsSupportReflection`). The cup product factors as
`α ∪ β = β ≫ Q` for `Q : Ri₂_! Ri₂^! N ⟶ Ri_! Ri^! (M ⊗ N)`. It suffices to show that the
restriction of `α ∪ β` to `Z₁` is a reflection into the objects supported on `Z'`, and there
`Li₁^* Q` is identified with the restriction of supports `ψ` along `i₁` followed by `Rj_! Rj^!` of
an isomorphism `Li₁^* N ≅ Li₁^* Ri₁_! Ri₁^! (M ⊗ N)` built from `α`
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_supportedProduct_comp`). Since
`β|_{Z₁} = Li₁^* β ≫ ψ` is a reflection, so is the restriction of `α ∪ β`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_supportedPullbackForget`
- `AlgebraicGeometry.Etale.isIso_supportedClassMap_cupWithSupports`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section PullbackForget

variable {U Z₁ Z Z' : Scheme.{u}} (i₁ : Z₁ ⟶ U) (i : Z ⟶ U) (j : Z' ⟶ Z₁)
  [IsClosedImmersion i₁] [IsClosedImmersion i] [IsClosedImmersion j]

/-- The derived direct image `Ri₁_* S` of an object `S` of `D(Z₁)` supported on `Z'` is supported
on `Z`, if `Z'` maps into `Z`. -/
lemma isZero_leftDerivedUpperStar_openComplement_rightDerivedLowerStar_of_isZero
    (hji : Set.range (j ≫ i₁).base ⊆ Set.range i.base)
    (S : DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hS : IsZero ((L((j.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj S)) :
    IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((R((i₁)_*[ModuleCat.{u + 1} Λ])).obj S)) := by
  have := isIso_counit_app_of_isZero Λ j S hS
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) j
  obtain ⟨e'⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) (j ≫ i₁)
  let φ : (R((i₁)_*[ModuleCat.{u + 1} Λ])).obj S ≅
      (R(j ≫ i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(j)^![Λ]).obj S) :=
    (R((i₁)_*[ModuleCat.{u + 1} Λ])).mapIso
        ((asIso ((rightDerivedUpperShriekAdjunction Λ j).counit.app S)).symm ≪≫ e.app _) ≪≫
      (rightDerivedLowerStarComp _ j i₁).app _ ≪≫ (e'.app _).symm
  exact (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint _ (j ≫ i₁) _ _
    ((disjoint_range_openComplement_ι i).mono_right hji)).of_iso
      ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).mapIso φ)

/-- The restriction to `Z₁` of the forgetful map `Ri_! Ri^! L ⟶ Ri₁_! Ri₁^! L`, read as a class
supported on `Z'` (`AlgebraicGeometry.Etale.supportedPullbackForget`), is an isomorphism when `Z'`
and `Z` have the same image in `U`: both `Li₁^* Ri_! Ri^! L ⟶ Li₁^* Ri₁_! Ri₁^! L` and the
counit of `Rj_! ⊣ Rj^!` are coreflections into the objects supported on `Z'`. -/
theorem isIso_supportedPullbackForget (hsub : Set.range i.base ⊆ Set.range i₁.base)
    (hd : Disjoint (Set.range (j.openComplement.ι ≫ i₁).base) (Set.range i.base))
    (hji : Set.range (j ≫ i₁).base ⊆ Set.range i.base)
    (L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (supportedPullbackForget Λ i i₁ j hsub hd L) := by
  set κ := supportedForget Λ i i₁ hsub L
  refine isIso_of_comp_counit_of_bijective _ j
    (isZero_leftDerivedUpperStar_openComplement_leftDerivedUpperStar_of_disjoint _ i₁ i j hd _)
    ((L((i₁)^*[ModuleCat.{u + 1} Λ])).map κ) ?_ _
    (supportedPullbackForget_comp_counit Λ i i₁ j hsub hd L)
  intro S hS
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i₁
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion Λ i₁
  set S₁ := (R((i₁)_*[ModuleCat.{u + 1} Λ])).obj S
  have hS₁ := isZero_leftDerivedUpperStar_openComplement_rightDerivedLowerStar_of_isZero Λ i₁ i j
    hji S hS
  have hS₁' := isZero_leftDerivedUpperStar_openComplement_rightDerivedLowerStar Λ i₁ S
  have hW := isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint
    (ModuleCat.{u + 1} Λ) i ((R(i)^![Λ]).obj L) _
    ((disjoint_range_openComplement_ι i₁).mono_right hsub)
  have hC := isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint
    (ModuleCat.{u + 1} Λ) i₁ ((R(i₁)^![Λ]).obj L) _
    (disjoint_range_openComplement_ι i₁)
  let c : (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj S₁ ≅ S := asIso (adj.counit.app S)
  have hκ : Function.Bijective (fun f : S₁ ⟶ _ ↦ f ≫ κ) := by
    have key : (fun f : S₁ ⟶ _ ↦
        f ≫ (rightDerivedUpperShriekAdjunction Λ i₁).counit.app L) ∘
          (fun f : S₁ ⟶ _ ↦ f ≫ κ) =
        (fun f ↦ f ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app L) := by
      funext f
      simp only [Function.comp_apply, Category.assoc, κ, supportedForget_comp_counit]
    exact ((bijective_comp_counit_of_isZero Λ i₁ S₁ hS₁' L).of_comp_iff' _).1
      ((congrArg Function.Bijective key).mpr (bijective_comp_counit_of_isZero Λ i S₁ hS₁ L))
  have key : (fun f : S ⟶ _ ↦ f ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map κ) ∘
      ((fun g ↦ c.inv ≫ g) ∘ (fun f : S₁ ⟶ _ ↦ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map f)) =
      ((fun g ↦ c.inv ≫ g) ∘ (fun f : S₁ ⟶ _ ↦ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map f)) ∘
        (fun f ↦ f ≫ κ) := by
    funext f
    simp only [Function.comp_apply, Category.assoc, Functor.map_comp]
  exact (Function.Bijective.of_comp_iff _ ((bijective_comp_left_of_isIso c.inv).comp
    (bijective_leftDerivedUpperStar_map_of_isZero Λ i₁ _ hW S₁))).1
      ((congrArg Function.Bijective key).mpr (((bijective_comp_left_of_isIso c.inv).comp
        (bijective_leftDerivedUpperStar_map_of_isZero Λ i₁ _ hC S₁)).comp hκ))

end PullbackForget

section Cup

omit [Finite Λ] in
/-- Naturality of the inverse of the left unitor of `Λ_X ⊗ -`, with the unit written as the
constant complex. -/
@[reassoc]
lemma derivedTensorLeftUnitor_inv_comp_derivedTensorHom_constantComplex {X : Scheme.{u}}
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (f : K ⟶ K') :
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X K).inv ≫
        derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 (constantComplex Λ X)) f =
      f ≫ (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X K').inv :=
  derivedTensorLeftUnitor_inv_comp_derivedTensorHom_id f

variable {U Z₁ Z₂ Z Z' : Scheme.{u}}

variable {Λ} in
/-- **The adjoint of a cup product.** Let `i₁ : Z₁ ⟶ U`, `i₂ : Z₂ ⟶ U` and `i : Z ⟶ U` be closed
immersions with `Z = Z₁ ∩ Z₂`, and `j : Z' ⟶ Z₁`, `g : Z' ⟶ Z₂` the base change of `i₂` along
`i₁`. Let `α : Λ_U ⟶ Ri₁_! Ri₁^! M` and `β : Λ_U ⟶ Ri₂_! Ri₂^! N` be classes with supports, with
`N` invertible, and `Δ` a section of the left unitor of `Λ_U`. If the adjoint
`Λ_{Z₁} ⟶ Ri₁^! M` of `α` is an isomorphism and the adjoint `Λ_{Z'} ⟶ Rj^! L'` of the
restriction of `β` to `Z₁` (along `τ : Li₁^* N ≅ L'`) is an isomorphism, then the adjoint
`Λ_Z ⟶ Ri^! (M ⊗ N)` of the cup product `α ∪ β` is an isomorphism. -/
theorem isIso_supportedClassMap_cupWithSupports
    (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U) (j : Z' ⟶ Z₁) (g : Z' ⟶ Z₂)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i] [IsClosedImmersion j]
    (hg : IsPullback g j i₂ i₁)
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    {M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hN : DerivedCategory.isInvertible Λ U N)
    (L' : DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (τ : (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj N ≅ L')
    (Δ : constantComplex Λ U ⟶
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj (constantComplex Λ U)).obj
        (constantComplex Λ U))
    (hΔ : Δ ≫ (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U _).hom = 𝟙 _)
    (α : constantComplex Λ U ⟶
      (R(i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(i₁)^![Λ]).obj M))
    (β : constantComplex Λ U ⟶
      (R(i₂)_![ModuleCat.{u + 1} Λ]).obj ((R(i₂)^![Λ]).obj N))
    (hα : IsIso (supportedClassMap Λ i₁ α))
    (hβ : IsIso (supportedClassMap Λ j (restrictSupportedClass Λ i₁ i₂ j g hg
      (leftDerivedUpperStarConstantComplexIso Λ i₁).inv τ β))) :
    IsIso (supportedClassMap Λ i (cupWithSupports Λ i₁ i₂ i h Δ α β)) := by
  have hsub : Set.range i.base ⊆ Set.range i₁.base := h ▸ Set.inter_subset_left
  have hd := disjoint_range_openComplement_ι_comp_of_isPullback_of_subset hg
    (h ▸ Set.inter_subset_right)
  have hji : Set.range (j ≫ i₁).base ⊆ Set.range i.base := by
    rintro _ ⟨z, rfl⟩
    rw [h, Scheme.Hom.comp_apply]
    exact ⟨⟨j z, rfl⟩, ⟨g z, by rw [← Scheme.Hom.comp_apply, hg.w, Scheme.Hom.comp_apply]⟩⟩
  obtain ⟨N', ⟨e⟩, ⟨e'⟩⟩ := hN
  have hΔ' : Δ = (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U _).inv :=
    (Iso.comp_hom_eq_id _).1 hΔ
  -- `α ∪ β = β ≫ Q`
  have hcup : cupWithSupports Λ i₁ i₂ i h Δ α β =
      β ≫ (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U _).inv ≫
        derivedTensorHom (ModuleCat.{u + 1} Λ) α (𝟙 _) ≫
          supportedProduct Λ i₁ i₂ i h M N := by
    have : derivedTensorHom (ModuleCat.{u + 1} Λ) α β =
        derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 _) β ≫
          derivedTensorHom (ModuleCat.{u + 1} Λ) α (𝟙 _) := by
      rw [derivedTensorHom_comp, Category.id_comp, Category.comp_id]
    rw [cupWithSupports_eq, hΔ', this, Category.assoc,
      derivedTensorLeftUnitor_inv_comp_derivedTensorHom_constantComplex_assoc]
  -- the product of `α` with `N` restricts to an isomorphism on `Z₁`
  have hαr := (isIso_supportedClassMap_iff_isSupportReflection Λ α).1 hα
  have hα' : IsIso ((L((i₁)^*[ModuleCat.{u + 1} Λ])).map α) :=
    hαr.isIso_leftDerivedUpperStar_map
      (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint _ i₁ _ _
        (disjoint_range_openComplement_ι i₁))
  have hPi := isIso_supportedTensorRight Λ i₁ e e' M
  have hαN : IsIso ((L((i₁)^*[ModuleCat.{u + 1} Λ])).map
      (derivedTensorHom (ModuleCat.{u + 1} Λ) α (𝟙 N))) := by
    have hn := leftDerivedUpperStarTensorIso_hom_naturality_left i₁ α N
    have : derivedTensorHom (ModuleCat.{u + 1} Λ) α (𝟙 N) =
        ((derivedTensor (ModuleCat.{u + 1} Λ) U).map α).app N := by
      simp only [derivedTensorHom, CategoryTheory.Functor.map_id, Category.comp_id]
    rw [this]
    have : IsIso ((L((i₁)^*[ModuleCat.{u + 1} Λ])).map
        (((derivedTensor (ModuleCat.{u + 1} Λ) U).map α).app N) ≫
          (leftDerivedUpperStarTensorIso _ i₁ _ N).hom) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (leftDerivedUpperStarTensorIso _ i₁ _ N).hom
  have hc : IsIso (τ.inv ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map
      ((derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U N).inv ≫
        derivedTensorHom (ModuleCat.{u + 1} Λ) α (𝟙 N) ≫
          supportedTensorRight Λ i₁ M N)) := by
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  -- reduce to the restriction to `Z₁`
  rw [isIso_supportedClassMap_iff_isSupportReflection, hcup]
  refine IsSupportReflection.of_leftDerivedUpperStar i₁ j hsub hd
    (leftDerivedUpperStarConstantComplexIso Λ i₁).inv ?_
  have := isIso_supportedPullbackForget Λ i₁ i j hsub hd hji
    (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj M).obj N)
  refine IsSupportReflection.of_comp_iso
    (asIso (supportedPullbackForget Λ i i₁ j hsub hd _)) ?_
  rw [asIso_hom, Functor.map_comp, Category.assoc, Category.assoc,
    leftDerivedUpperStar_map_supportedProduct_comp Λ i₁ i₂ i h j g hg M N L' τ
      α]
  have hβr := (isIso_supportedClassMap_iff_isSupportReflection Λ _).1 hβ
  have := hβr.comp_iso ((R(j)_![ModuleCat.{u + 1} Λ]).mapIso
    ((R(j)^![Λ]).mapIso (asIso (τ.inv ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map
      ((derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U N).inv ≫
        derivedTensorHom (ModuleCat.{u + 1} Λ) α (𝟙 N) ≫
          supportedTensorRight Λ i₁ M N)))))
  simpa only [restrictSupportedClass, Category.assoc, Functor.mapIso_hom, asIso_hom] using this

end Cup

end Etale

end AlgebraicGeometry
