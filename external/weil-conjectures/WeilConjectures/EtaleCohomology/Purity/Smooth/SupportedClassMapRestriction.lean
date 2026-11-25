/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass

/-!
# The adjoint of a class with supports under restriction of supports

Let `i : Z ⟶ X` be a closed immersion, `e : U ⟶ X` a morphism and `i' : Z' ⟶ U`, `g : Z' ⟶ Z`
the base change of `i` along `e`. A class `γ : Λ_X ⟶ Ri_! Ri^! L` supported on `Z` restricts
to a class `γ'` supported on `Z'` (`AlgebraicGeometry.Etale.restrictSupportedClass`). We show
that when the restriction of supports `ψ : Le^* Ri_! Ri^! L ⟶ Ri'_! Ri'^! L'` is an
isomorphism, the adjoint `Λ_{Z'} ⟶ Ri'^! L'` of `γ'` is an isomorphism if and only if the
pullback `Lg^* (Λ_Z ⟶ Ri^! L)` of the adjoint of `γ` is one
(`AlgebraicGeometry.Etale.supportedClassMap`).

The argument avoids computing base change maps. The adjoint `γ ↦ (Λ_Z ⟶ N)` is a bijection
`Hom(Λ_X, Ri_! N) ≅ Hom(Λ_Z, N)` natural in `N` (`AlgebraicGeometry.Etale.supportedTranspose`),
so `γ = u ≫ Ri_!(φ)` for the *restriction map* `u : Λ_X ⟶ Ri_! Λ_Z` corresponding to the
identity, where `φ` is the adjoint of `γ`. As `Ri_!` is fully faithful, `u` is a reflection of
`Λ_X` into the objects of the form `Ri_! N`. Pulling back along `e`, the map
`Λ_U ≅ Le^* Λ_X ⟶ Le^* Ri_! Λ_Z` is again such a reflection, now for `i'`: by adjunction this
amounts to `Re_* Ri'_! N ≅ Ri_! Rg_* N`. Two reflections agree up to a unique isomorphism, so
`Ri'_!` of the adjoint of `γ'` is `Le^* Ri_!(φ) ≫ ψ` up to isomorphism, and `Ri'_!` is fully
faithful. Finally `Le^* Ri_! B` is supported on `Z'`, where `Li'^*` reflects isomorphisms, and
`Li'^* Le^* Ri_! ≅ Lg^* Li^* Ri_! ≅ Lg^*` since `Li^* Ri_* ≅ 𝟭` for the closed immersion `i`.

## Main definitions

- `AlgebraicGeometry.Etale.supportedTranspose`: the adjoint `Λ_Z ⟶ N` of `Λ_X ⟶ Ri_! N`.
- `AlgebraicGeometry.Etale.supportedRestrictionMap`: the restriction map `Λ_X ⟶ Ri_! Λ_Z`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_supportedClassMap_restrictSupportedClass_iff`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section FullyFaithful

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
  [IsClosedImmersion i]

/-- For a closed immersion `i`, the derived lower shriek `Ri_!` is fully faithful: the unit of
`Ri_! ⊣ Ri^!` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_unit_app`). -/
noncomputable def fullyFaithfulRightDerivedLowerShriek :
    (R(i)_![ModuleCat.{u + 1} Λ]).FullyFaithful :=
  have (Q : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsIso ((rightDerivedUpperShriekAdjunction Λ i).unit.app Q) :=
    isIso_rightDerivedUpperShriekAdjunction_unit_app Λ i Q
  have : IsIso (rightDerivedUpperShriekAdjunction Λ i).unit := NatIso.isIso_of_isIso_app _
  (rightDerivedUpperShriekAdjunction Λ i).fullyFaithfulLOfIsIsoUnit

instance full_rightDerivedLowerShriek : (R(i)_![ModuleCat.{u + 1} Λ]).Full :=
  (fullyFaithfulRightDerivedLowerShriek Λ i).full

instance faithful_rightDerivedLowerShriek : (R(i)_![ModuleCat.{u + 1} Λ]).Faithful :=
  (fullyFaithfulRightDerivedLowerShriek Λ i).faithful

end FullyFaithful

lemma bijective_comp_left_of_isIso {C : Type*} [Category C] {P Q T : C} (c : P ⟶ Q)
    [IsIso c] : Function.Bijective (fun f : Q ⟶ T ↦ c ≫ f) :=
  ⟨fun _ _ h ↦ (cancel_epi c).1 h, fun f ↦ ⟨inv c ≫ f, by simp⟩⟩

lemma bijective_comp_right_of_isIso {C : Type*} [Category C] {B T T' : C} (c : T ⟶ T')
    [IsIso c] : Function.Bijective (fun f : B ⟶ T ↦ f ≫ c) :=
  ⟨fun _ _ h ↦ (cancel_mono c).1 h, fun f ↦ ⟨f ≫ inv c, by simp⟩⟩

/-- If precomposition with `w` is a bijection onto `Hom(-, T')`, it is one onto `Hom(-, T)` for
any `T ≅ T'`. -/
lemma bijective_comp_of_iso {C : Type*} [Category C] {P B T T' : C} (w : P ⟶ B) (θ : T ≅ T')
    (h : Function.Bijective (fun f : B ⟶ T' ↦ w ≫ f)) :
    Function.Bijective (fun f : B ⟶ T ↦ w ≫ f) := by
  have : (fun f : B ⟶ T ↦ w ≫ f) =
      (fun f ↦ f ≫ θ.inv) ∘ (fun f : B ⟶ T' ↦ w ≫ f) ∘ (fun f ↦ f ≫ θ.hom) := by
    funext f
    simp
  rw [this]
  exact (bijective_comp_right_of_isIso θ.inv).comp
    (h.comp (bijective_comp_right_of_isIso θ.hom))

variable (Λ : Type (u + 1)) [CommRing Λ]

section Transpose

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The *adjoint* `Λ_Z ⟶ N` of a morphism `γ : Λ_X ⟶ Ri_! N`, for a closed immersion
`i : Z ⟶ X`: the transpose of `γ` along the forget-supports map `Ri_! ⟶ Ri_*`, read through
`Li^* Λ_X ≅ Λ_Z`. For `N = Ri^! L` it is `AlgebraicGeometry.Etale.supportedClassMap`. -/
noncomputable def supportedTranspose
    {N : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj N) :
    constantComplex Λ Z ⟶ N :=
  (compactificationConstantComplexIso Λ i).inv ≫
    rightDerivedLowerShriekTranspose (ModuleCat.{u + 1} Λ) i γ

lemma supportedClassMap_eq_supportedTranspose [Finite Λ]
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    supportedClassMap Λ i γ = supportedTranspose Λ i γ :=
  rfl

/-- The adjoint `Hom(Λ_X, Ri_! N) ⟶ Hom(Λ_Z, N)` is a bijection. -/
theorem supportedTranspose_bijective
    (N : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Function.Bijective (supportedTranspose Λ i (N := N)) := by
  let E := ((Iso.refl _).homCongr (asIso ((rightDerivedLowerShriekToLowerStarComp
      (ModuleCat.{u + 1} Λ) i).app N))).trans
    ((((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) _).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) _)).homEquiv _ _).symm.trans
        ((compactificationConstantComplexIso Λ i).homCongr (Iso.refl _)))
  convert E.bijective using 1
  ext γ
  simp [E, supportedTranspose, rightDerivedLowerShriekTranspose]

/-- The adjoint is natural in the coefficients. -/
theorem supportedTranspose_comp
    {N N' : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj N) (f : N ⟶ N') :
    supportedTranspose Λ i (γ ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map f) =
      supportedTranspose Λ i γ ≫ f := by
  simp only [supportedTranspose, rightDerivedLowerShriekTranspose, Category.assoc]
  have := (rightDerivedLowerShriekToLowerStarComp (ModuleCat.{u + 1} Λ) i).naturality f
  rw [this, ← Category.assoc, Adjunction.homEquiv_naturality_right_symm]

/-- The *restriction map* `Λ_X ⟶ Ri_! Λ_Z`: the morphism whose adjoint is the identity. -/
noncomputable def supportedRestrictionMap :
    constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z) :=
  (Equiv.ofBijective _ (supportedTranspose_bijective Λ i _)).symm (𝟙 _)

lemma supportedTranspose_supportedRestrictionMap :
    supportedTranspose Λ i (supportedRestrictionMap Λ i) = 𝟙 _ :=
  (Equiv.ofBijective _ (supportedTranspose_bijective Λ i _)).apply_symm_apply _

/-- Every morphism `γ : Λ_X ⟶ Ri_! N` is the restriction map followed by `Ri_!` of its
adjoint. -/
theorem supportedRestrictionMap_comp_map_supportedTranspose
    {N : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj N) :
    supportedRestrictionMap Λ i ≫
        (R(i)_![ModuleCat.{u + 1} Λ]).map (supportedTranspose Λ i γ) = γ := by
  apply (supportedTranspose_bijective Λ i N).injective
  rw [supportedTranspose_comp, supportedTranspose_supportedRestrictionMap, Category.id_comp]

/-- The restriction map `Λ_X ⟶ Ri_! Λ_Z` is a reflection of `Λ_X` into the objects of the form
`Ri_! N`: precomposition with it is a bijection `Hom(Ri_! Λ_Z, Ri_! N) ≅ Hom(Λ_X, Ri_! N)`. -/
theorem bijective_supportedRestrictionMap_comp [Finite Λ]
    (N : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Function.Bijective (fun h : (R(i)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z) ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj N ↦ supportedRestrictionMap Λ i ≫ h) := by
  have hF := fullyFaithfulRightDerivedLowerShriek Λ i
  have : (fun h : (R(i)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z) ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj N ↦ supportedRestrictionMap Λ i ≫ h) =
      (Equiv.ofBijective _ (supportedTranspose_bijective Λ i N)).symm ∘ hF.homEquiv.symm := by
    funext h
    apply (Equiv.ofBijective _ (supportedTranspose_bijective Λ i N)).injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Equiv.ofBijective_apply]
    conv_lhs => rw [← hF.map_preimage h]
    rw [supportedTranspose_comp, supportedTranspose_supportedRestrictionMap, Category.id_comp]
    rfl
  rw [this]
  exact (Equiv.bijective _).comp (Equiv.bijective _)

end Transpose

section Restriction

variable {U X Z Z' : Scheme.{u}} (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U) [IsClosedImmersion i]
  [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)

include hg in
/-- The pushforward `Re_* Ri'_! N` is of the form `Ri_! M`, namely for `M = Rg_* N`. -/
lemma nonempty_iso_rightDerivedLowerStar_obj_rightDerivedLowerShriek_obj
    (N : DerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R((e)_*[ModuleCat.{u + 1} Λ])).obj ((R(i')_![ModuleCat.{u + 1} Λ]).obj N) ≅
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R((g)_*[ModuleCat.{u + 1} Λ])).obj N)) := by
  obtain ⟨a⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) i'
  obtain ⟨b⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) i
  exact ⟨(R((e)_*[ModuleCat.{u + 1} Λ])).mapIso (a.app N) ≪≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) i' e).app N ≪≫
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} Λ) hg.w.symm).app N ≪≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) g i).symm.app N ≪≫ (b.app _).symm⟩

include hg in
/-- The pullback `Λ_U ≅ Le^* Λ_X ⟶ Le^* Ri_! Λ_Z` of the restriction map is a reflection of
`Λ_U` into the objects of the form `Ri'_! N`. -/
theorem bijective_leftDerivedUpperStar_map_supportedRestrictionMap_comp
    [Finite Λ]
    (N : DerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Function.Bijective (fun h : (L((e)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z)) ⟶
          (R(i')_![ModuleCat.{u + 1} Λ]).obj N ↦
      (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
        (L((e)^*[ModuleCat.{u + 1} Λ])).map (supportedRestrictionMap Λ i) ≫ h) := by
  obtain ⟨θ⟩ := nonempty_iso_rightDerivedLowerStar_obj_rightDerivedLowerShriek_obj Λ e i i' g hg N
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e
  have h₁ := bijective_comp_of_iso (supportedRestrictionMap Λ i) θ
    (bijective_supportedRestrictionMap_comp Λ i _)
  have : (fun h : (L((e)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z)) ⟶
          (R(i')_![ModuleCat.{u + 1} Λ]).obj N ↦
      (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
        (L((e)^*[ModuleCat.{u + 1} Λ])).map (supportedRestrictionMap Λ i) ≫ h) =
      (fun f ↦ (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫ f) ∘
        (adj.homEquiv _ _).symm ∘ (fun f ↦ supportedRestrictionMap Λ i ≫ f) ∘
          adj.homEquiv _ _ := by
    funext h
    simp only [Function.comp_apply]
    rw [← Adjunction.homEquiv_naturality_left, Equiv.symm_apply_apply]
  rw [this]
  exact (bijective_comp_left_of_isIso _).comp
    ((adj.homEquiv _ _).symm.bijective.comp (h₁.comp (adj.homEquiv _ _).bijective))

include hg in
/-- The pullback `Le^* Ri_! B` is supported on `Z'`: it vanishes on the open complement of `Z'`,
which misses the preimage of `Z`. -/
lemma isZero_leftDerivedUpperStar_openComplement_obj
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsZero ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((L((e)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj B))) := by
  refine (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint _ i
    i.openComplement.ι
    (by rw [i.range_eq_compl_range_openComplement_ι]; exact disjoint_compl_left)
    (i'.openComplement.ι ≫ e) ?_ _).of_iso
      ((leftDerivedUpperStarComp _ i'.openComplement.ι e).app _).symm
  rw [← compl_compl (Set.range i.openComplement.ι), ← i.range_eq_compl_range_openComplement_ι,
    Set.subset_compl_iff_disjoint_left, Set.disjoint_left]
  rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
  apply x.2
  rw [Scheme.range_snd_of_isPullback hg]
  exact ⟨z, hx.symm⟩

omit [IsClosedImmersion i] in
/-- The counit `Ri'_! Ri'^! K ⟶ K` is an isomorphism for `K` supported on `Z'`, by the supported
localization triangle. -/
lemma isIso_counit_app_of_isZero [Finite Λ]
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    IsIso ((rightDerivedUpperShriekAdjunction Λ i').counit.app K) :=
  (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    (supportedLocalizationTriangle_mem_distTriang _ i' i'.openComplement.ι
      i'.range_eq_compl_range_openComplement_ι K)).1
    ((R((i'.openComplement.ι)_*[ModuleCat.{u + 1} Λ])).map_isZero hK)

omit [IsClosedImmersion i] in
/-- For a closed immersion `i`, the counit `Li^* Ri_* ⟶ 𝟭` is an isomorphism. -/
lemma isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion :
    IsIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i').counit := by
  have : ((i')_*[ModuleCat.{u + 1} Λ]).PreservesKInjectiveComplexes :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i').preservesKInjectiveComplexes
  exact
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i').counit_isIso_of_R_fully_faithful

omit [IsClosedImmersion i] in
/-- `Li'^*` reflects isomorphisms between objects supported on `Z'`. -/
lemma isIso_of_isIso_leftDerivedUpperStar_map_of_isZero
    [Finite Λ]
    {K₁ K₂ : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK₁ : IsZero ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj K₁))
    (hK₂ : IsZero ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj K₂)) (f : K₁ ⟶ K₂)
    (hf : IsIso ((L((i')^*[ModuleCat.{u + 1} Λ])).map f)) : IsIso f := by
  let adj := rightDerivedUpperShriekAdjunction Λ i'
  have := isIso_counit_app_of_isZero Λ i' K₁ hK₁
  have := isIso_counit_app_of_isZero Λ i' K₂ hK₂
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion Λ i'
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) i'
  let E : R(i')_![ModuleCat.{u + 1} Λ] ⋙ L((i')^*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
    Functor.isoWhiskerRight c _ ≪≫
      asIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i').counit
  have key : (R(i')_![ModuleCat.{u + 1} Λ]).map ((R(i')^![Λ]).map f) ≫
      adj.counit.app K₂ = adj.counit.app K₁ ≫ f := adj.counit_naturality f
  have h₁ : IsIso ((L((i')^*[ModuleCat.{u + 1} Λ])).map
      ((R(i')_![ModuleCat.{u + 1} Λ]).map ((R(i')^![Λ]).map f))) := by
    have h := congrArg (L((i')^*[ModuleCat.{u + 1} Λ])).map key
    rw [Functor.map_comp, Functor.map_comp] at h
    have : IsIso ((L((i')^*[ModuleCat.{u + 1} Λ])).map
        ((R(i')_![ModuleCat.{u + 1} Λ]).map ((R(i')^![Λ]).map f)) ≫
          (L((i')^*[ModuleCat.{u + 1} Λ])).map (adj.counit.app K₂)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((L((i')^*[ModuleCat.{u + 1} Λ])).map (adj.counit.app K₂))
  have h₂ : IsIso ((R(i')^![Λ]).map f) :=
    (NatIso.isIso_map_iff E ((R(i')^![Λ]).map f)).1 h₁
  have : IsIso (adj.counit.app K₁ ≫ f) := by
    rw [← key]
    infer_instance
  exact IsIso.of_isIso_comp_left (adj.counit.app K₁) f

include hg in
/-- `Le^* Ri_!(φ)` is an isomorphism if and only if `Lg^*(φ)` is one. -/
lemma isIso_leftDerivedUpperStar_map_rightDerivedLowerShriek_map_iff
    [Finite Λ]
    {B₁ B₂ : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : B₁ ⟶ B₂) :
    IsIso ((L((e)^*[ModuleCat.{u + 1} Λ])).map ((R(i)_![ModuleCat.{u + 1} Λ]).map φ)) ↔
      IsIso ((L((g)^*[ModuleCat.{u + 1} Λ])).map φ) := by
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) i
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion Λ i
  let E : L((g)^*[ModuleCat.{u + 1} Λ]) ≅ R((i)_*[ModuleCat.{u + 1} Λ]) ⋙
      L((e)^*[ModuleCat.{u + 1} Λ]) ⋙ L((i')^*[ModuleCat.{u + 1} Λ]) :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((leftDerivedUpperStarComp _ g i).symm ≪≫
        leftDerivedUpperStarComp _ i' e (g ≫ i) hg.w)
  have hsupp (B : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsZero ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((e)^*[ModuleCat.{u + 1} Λ])).obj ((R((i)_*[ModuleCat.{u + 1} Λ])).obj B))) :=
    (isZero_leftDerivedUpperStar_openComplement_obj Λ e i i' g hg B).of_iso
      ((L((i'.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).mapIso
        ((L((e)^*[ModuleCat.{u + 1} Λ])).mapIso (c.app B))).symm
  refine (NatIso.isIso_map_iff
    (Functor.isoWhiskerRight c (L((e)^*[ModuleCat.{u + 1} Λ]))) φ).trans
    (Iff.trans ?_ (NatIso.isIso_map_iff E φ).symm)
  constructor
  · intro h
    have : IsIso ((L((e)^*[ModuleCat.{u + 1} Λ])).map ((R((i)_*[ModuleCat.{u + 1} Λ])).map φ)) := h
    exact Functor.map_isIso (L((i')^*[ModuleCat.{u + 1} Λ])) _
  · intro h
    exact isIso_of_isIso_leftDerivedUpperStar_map_of_isZero Λ i' (hsupp B₁) (hsupp B₂) _ h

include hg in
/-- **Restriction of supports and adjoints.** Let `i' : Z' ⟶ U`, `g : Z' ⟶ Z` be the base
change of a closed immersion `i : Z ⟶ X` along `e : U ⟶ X`, let `γ : Λ_X ⟶ Ri_! Ri^! L` be a
class supported on `Z` with adjoint `φ : Λ_Z ⟶ Ri^! L`, and let `τ : Le^* L ≅ L'`. If the
restriction of supports `Le^* Ri_! Ri^! L ⟶ Ri'_! Ri'^! L'` is an isomorphism, then the adjoint
of the restricted class `γ'` is an isomorphism if and only if `Lg^* φ` is one.

Indeed `Ri'_!` of the adjoint of `γ'` is, up to isomorphisms, `Le^* Ri_!(φ)` followed by the
restriction of supports. As `Le^* Ri_! B` is supported on `Z'`, `Le^* Ri_!(φ)` is an isomorphism
if and only if `Li'^* Le^* Ri_!(φ) ≅ Lg^* Li^* Ri_!(φ) ≅ Lg^*(φ)` is one. -/
theorem isIso_supportedClassMap_restrictSupportedClass_iff [Finite Λ]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L')
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj L))
    (hψ : IsIso (supportedRestriction Λ e i i' g hg L L' τ)) :
    IsIso (supportedClassMap Λ i' (restrictSupportedClass Λ e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv τ γ)) ↔
      IsIso ((L((g)^*[ModuleCat.{u + 1} Λ])).map (supportedClassMap Λ i γ)) := by
  set ψ := supportedRestriction Λ e i i' g hg L L' τ
  set φ := supportedClassMap Λ i γ
  set φ' := supportedClassMap Λ i' (restrictSupportedClass Λ e i i' g hg
    (leftDerivedUpperStarConstantComplexIso Λ e).inv τ γ)
  set v := (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
    (L((e)^*[ModuleCat.{u + 1} Λ])).map (supportedRestrictionMap Λ i)
  set u' := supportedRestrictionMap Λ i'
  have := isIso_counit_app_of_isZero Λ i' _
    (isZero_leftDerivedUpperStar_openComplement_obj Λ e i i' g hg (constantComplex Λ Z))
  let βP := (asIso ((rightDerivedUpperShriekAdjunction Λ i').counit.app
    ((L((e)^*[ModuleCat.{u + 1} Λ])).obj
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z))))).symm
  have hu' : ∀ {T} N, (T ≅ (R(i')_![ModuleCat.{u + 1} Λ]).obj N) →
      Function.Bijective (fun f : _ ⟶ T ↦ u' ≫ f) := fun N θ ↦
    bijective_comp_of_iso u' θ (bijective_supportedRestrictionMap_comp Λ i' N)
  have hv : ∀ {T} N, (T ≅ (R(i')_![ModuleCat.{u + 1} Λ]).obj N) →
      Function.Bijective (fun f : _ ⟶ T ↦ v ≫ f) := fun N θ ↦ by
    refine bijective_comp_of_iso v θ ?_
    simpa only [v, Category.assoc] using
      bijective_leftDerivedUpperStar_map_supportedRestrictionMap_comp Λ e i i' g hg N
  obtain ⟨a, ha⟩ := (hu' _ βP).2 v
  obtain ⟨b, hb⟩ := (hv _ (Iso.refl _)).2 u'
  dsimp only at ha hb
  have hab : a ≫ b = 𝟙 _ := (hu' _ (Iso.refl _)).1 (by
    dsimp only
    rw [← Category.assoc, ha, hb, Category.comp_id])
  have hba : b ≫ a = 𝟙 _ := (hv _ βP).1 (by
    dsimp only
    rw [← Category.assoc, hb, ha, Category.comp_id])
  have : IsIso a := ⟨b, hab, hba⟩
  have hγ : supportedRestrictionMap Λ i ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map φ = γ :=
    supportedRestrictionMap_comp_map_supportedTranspose Λ i γ
  have key : (R(i')_![ModuleCat.{u + 1} Λ]).map φ' =
      a ≫ (L((e)^*[ModuleCat.{u + 1} Λ])).map ((R(i)_![ModuleCat.{u + 1} Λ]).map φ) ≫ ψ := by
    apply (hu' _ (Iso.refl _)).1
    refine (supportedRestrictionMap_comp_map_supportedTranspose Λ i' _).trans ?_
    dsimp only
    rw [← Category.assoc u' a, ha]
    simp only [restrictSupportedClass, v, Category.assoc, ← Functor.map_comp_assoc, hγ, ψ]
  rw [← isIso_iff_of_reflects_iso φ' (R(i')_![ModuleCat.{u + 1} Λ]), key, isIso_comp_left_iff,
    isIso_comp_right_iff]
  exact isIso_leftDerivedUpperStar_map_rightDerivedLowerShriek_map_iff Λ e i i' g hg φ

end Restriction

end Etale

end AlgebraicGeometry
