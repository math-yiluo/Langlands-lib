/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc

/-!
# Tensoring classes with supports by coefficients

Let `i₁ : Z₁ ⟶ U` be a closed immersion. Write `C₁ L = Ri₁_! Ri₁^! L` for the coreflection of
`L ∈ D(U_ét)` into the objects supported on `Z₁`, with counit `ε₁ : C₁ L ⟶ L`. This file provides
the comparison maps relating the cup product with supports
(`AlgebraicGeometry.Etale.supportedProduct`) to its restriction to `Z₁`, which compute the adjoint
of a cup product of classes in `AlgebraicGeometry.Etale.isIso_supportedClassMap_cupWithSupports`:

* the *product with coefficients* `Π : C₁ M ⊗ N ⟶ C₁ (M ⊗ N)`, the lift of `ε₁ ⊗ N` through the
  counit (`AlgebraicGeometry.Etale.supportedTensorRight`). It is an isomorphism when `N` is
  `⊗`-invertible (`AlgebraicGeometry.Etale.isIso_supportedTensorRight`): tensoring with `N` is an
  equivalence preserving the objects supported on `Z₁`, so `ε₁ ⊗ N` is again a coreflection;
* the *forgetful map* `κ : C L ⟶ C₁ L` for a closed immersion `i : Z ⟶ U` with `Z ⊆ Z₁`
  (`AlgebraicGeometry.Etale.supportedForget`), and its restriction to `Z₁`,
  `ω : Li₁^* C L ⟶ Rj_! Rj^! (Li₁^* C₁ L)` for a closed immersion `j : Z' ⟶ Z₁` with the same
  range as `i` (`AlgebraicGeometry.Etale.supportedPullbackForget`).

The main identity (`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_supportedProduct_comp`)
says that, for classes `α : 𝟙 ⟶ C₁ M` and `β` supported on `Z₂`, the restriction to `Z₁` of the
map `T₂ ⟶ C(M ⊗ N)` through which `α ∪ β` factors is the restriction of supports along `i₁`
followed by `Rj_! Rj^!` of the restriction of `α ⊗ N`. All identities are proved by uniqueness
of lifts through counits.

## Main definitions

- `AlgebraicGeometry.Etale.supportedTensorRight`
- `AlgebraicGeometry.Etale.supportedForget`
- `AlgebraicGeometry.Etale.supportedPullbackForget`

## Main statements

- `AlgebraicGeometry.Etale.isIso_supportedTensorRight`
- `AlgebraicGeometry.Etale.supportedProduct_comp_supportedForget`
- `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_supportedProduct_comp`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Ranges

variable {U Z Z₁ Z₂ Z' : Scheme.{u}}

/-- The open complement of a closed immersion has the complementary range. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.range_openComplement_ι (i : Z ⟶ U)
    [IsClosedImmersion i] :
    Set.range i.openComplement.ι.base = (Set.range i.base)ᶜ := by
  rw [i.range_eq_compl_range_openComplement_ι, compl_compl]

/-- The open complement of `Z` misses `Z`. -/
lemma disjoint_range_openComplement_ι (i : Z ⟶ U) [IsClosedImmersion i] :
    Disjoint (Set.range i.openComplement.ι.base) (Set.range i.base) := by
  rw [Scheme.Hom.range_openComplement_ι]
  exact disjoint_compl_left

/-- In a pullback square of schemes, a point of `Z₁` mapping into the range of `i₂` comes from
the fibre product. -/
lemma mem_range_of_isPullback {i₁ : Z₁ ⟶ U} {i₂ : Z₂ ⟶ U} {j : Z' ⟶ Z₁} {g : Z' ⟶ Z₂}
    (hg : IsPullback g j i₂ i₁) {z : Z₁} (hz : i₁ z ∈ Set.range i₂.base) :
    z ∈ Set.range j.base := by
  obtain ⟨y, hy⟩ := hz
  obtain ⟨w, -, hw⟩ := hg.exists_scheme_point y z hy
  exact ⟨w, hw⟩

/-- In a pullback square `Z' = Z₁ ×_U Z₂`, the open complement of `Z'` in `Z₁` maps into the open
complement of `Z₂`. -/
lemma disjoint_range_openComplement_ι_comp_of_isPullback {i₁ : Z₁ ⟶ U} {i₂ : Z₂ ⟶ U}
    {j : Z' ⟶ Z₁} {g : Z' ⟶ Z₂} [IsClosedImmersion j] (hg : IsPullback g j i₂ i₁) :
    Disjoint (Set.range (j.openComplement.ι ≫ i₁).base) (Set.range i₂.base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ hx
  have hx' : j.openComplement.ι x ∈ Set.range j.base :=
    mem_range_of_isPullback hg (by rwa [Scheme.Hom.comp_apply] at hx)
  exact Set.disjoint_left.1 (disjoint_range_openComplement_ι j) ⟨x, rfl⟩ hx'

/-- If `Z ⊆ Z₂` (as subsets of `U`), then in a pullback square `Z' = Z₁ ×_U Z₂` the open
complement of `Z'` in `Z₁` misses `Z`. -/
lemma disjoint_range_openComplement_ι_comp_of_isPullback_of_subset {i₁ : Z₁ ⟶ U}
    {i₂ : Z₂ ⟶ U} {i : Z ⟶ U} {j : Z' ⟶ Z₁} {g : Z' ⟶ Z₂} [IsClosedImmersion j]
    (hg : IsPullback g j i₂ i₁) (h : Set.range i.base ⊆ Set.range i₂.base) :
    Disjoint (Set.range (j.openComplement.ι ≫ i₁).base) (Set.range i.base) :=
  (disjoint_range_openComplement_ι_comp_of_isPullback hg).mono_right h

end Ranges

section Support

variable {U Z₁ Z' W : Scheme.{u}}

/-- An object of the form `Ri_! B ⊗ N` restricts to zero on the open complement of `Z`. -/
lemma isZero_leftDerivedUpperStar_openComplement_derivedTensor_rightDerivedLowerShriek
    (i : Z₁ ⟶ U) [IsClosedImmersion i] (B : DerivedCategory (Sheaf Z₁.smallEtaleTopology A))
    (N : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    IsZero ((L((i.openComplement.ι)^*[A])).obj
      (((derivedTensor A U).obj ((R(i)_![A]).obj B)).obj N)) :=
  (isZero_derivedTensor_obj_obj_of_isZero_left
    (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint A i B _
      (disjoint_range_openComplement_ι i)) _).of_iso
    (leftDerivedUpperStarTensorIso A _ _ _)

/-- A tensor product `S ⊗ N` restricts to zero on the open complement of `Z` if `S` does. -/
lemma isZero_leftDerivedUpperStar_openComplement_derivedTensor
    (i : Z₁ ⟶ U) [IsClosedImmersion i] {S : DerivedCategory (Sheaf U.smallEtaleTopology A)}
    (hS : IsZero ((L((i.openComplement.ι)^*[A])).obj S))
    (N : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    IsZero ((L((i.openComplement.ι)^*[A])).obj (((derivedTensor A U).obj S).obj N)) :=
  (isZero_derivedTensor_obj_obj_of_isZero_left hS _).of_iso
    (leftDerivedUpperStarTensorIso A _ _ _)

/-- The pullback `Lw^* K` along `w ⟶ U` vanishes as soon as `w` factors through an open
`V ⟶ U` on which `K` vanishes. -/
lemma isZero_leftDerivedUpperStar_comp_of_isZero {V : Scheme.{u}} (v : V ⟶ U)
    {K : DerivedCategory (Sheaf U.smallEtaleTopology A)} (hK : IsZero ((L((v)^*[A])).obj K))
    (w : W ⟶ V) : IsZero ((L((w ≫ v)^*[A])).obj K) :=
  ((L((w)^*[A])).map_isZero hK).of_iso ((leftDerivedUpperStarComp A w v).app _)

/-- Let `j : Z' ⟶ Z₁` be a closed immersion and `i : Z ⟶ U` a closed immersion such that the open
complement of `Z'` maps into the open complement of `Z`. Then `Li₁^* Ri_! B` is supported on
`Z'`. -/
lemma isZero_leftDerivedUpperStar_openComplement_leftDerivedUpperStar_of_disjoint
    {Z : Scheme.{u}} (i₁ : Z₁ ⟶ U) (i : Z ⟶ U) (j : Z' ⟶ Z₁) [IsClosedImmersion i]
    [IsClosedImmersion j]
    (hd : Disjoint (Set.range (j.openComplement.ι ≫ i₁).base) (Set.range i.base))
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    IsZero ((L((j.openComplement.ι)^*[A])).obj ((L((i₁)^*[A])).obj ((R(i)_![A]).obj B))) :=
  (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint A i B _ hd).of_iso
    ((leftDerivedUpperStarComp A j.openComplement.ι i₁).app _).symm

end Support

section TensorRight

/-- Precomposition with an isomorphism is a bijection. -/
lemma bijective_iso_hom_comp {C : Type*} [Category* C] {P Q T : C} (c : P ≅ Q) :
    Function.Bijective (fun f : Q ⟶ T ↦ c.hom ≫ f) :=
  ⟨fun _ _ h ↦ (cancel_epi c.hom).1 h, fun f ↦ ⟨c.inv ≫ f, by simp⟩⟩

variable {U Z : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i]

/-- The lift of `ε ⊗ N : Ri_! Ri^! M ⊗ N ⟶ M ⊗ N` through the counit of `Ri_! ⊣ Ri^!` exists and
is unique, since the source is supported on `Z`. -/
theorem existsUnique_supportedTensorRight
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃! π : ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj M))).obj N ⟶
        (R(i)_![ModuleCat.{u + 1} Λ]).obj
          ((R(i)^![Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj M).obj N)),
      π ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app
          (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj M).obj N) =
        derivedTensorHom (ModuleCat.{u + 1} Λ)
          ((rightDerivedUpperShriekAdjunction Λ i).counit.app M) (𝟙 N) :=
  existsUnique_comp_counit_of_isZero Λ i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι
    (isZero_leftDerivedUpperStar_openComplement_derivedTensor_rightDerivedLowerShriek
      (ModuleCat.{u + 1} Λ) i _ N) _

/-- The *product of a supported object with coefficients*
`Ri_! Ri^! M ⊗ N ⟶ Ri_! Ri^! (M ⊗ N)`: the unique lift of `ε ⊗ N` through the counit. -/
noncomputable def supportedTensorRight
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj M))).obj N ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj M).obj N)) :=
  (existsUnique_supportedTensorRight Λ i M N).exists.choose

/-- The defining property of `AlgebraicGeometry.Etale.supportedTensorRight`. -/
@[reassoc]
lemma supportedTensorRight_comp_counit
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    supportedTensorRight Λ i M N ≫
        (rightDerivedUpperShriekAdjunction Λ i).counit.app
          (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj M).obj N) =
      derivedTensorHom (ModuleCat.{u + 1} Λ)
        ((rightDerivedUpperShriekAdjunction Λ i).counit.app M) (𝟙 N) :=
  (existsUnique_supportedTensorRight Λ i M N).exists.choose_spec

/-- **Comparison of coreflections.** Let `q : T ⟶ L` be a morphism out of an object supported on
`Z` through which every morphism from an object supported on `Z` to `L` factors uniquely. Then
the lift `T ⟶ Ri_! Ri^! L` of `q` through the counit is an isomorphism. -/
lemma isIso_of_comp_counit_of_bijective
    {T L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hT : IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj T)) (q : T ⟶ L)
    (hq : ∀ S : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj S) →
        Function.Bijective (fun f : S ⟶ T ↦ f ≫ q))
    (π : T ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))
    (hπ : π ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app L = q) : IsIso π := by
  set ε := (rightDerivedUpperShriekAdjunction Λ i).counit.app L
  have hC : IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L))) :=
    isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) i _ _
      (disjoint_range_openComplement_ι i)
  obtain ⟨σ, hσ⟩ := (hq _ hC).2 ε
  dsimp only at hσ
  refine ⟨σ, (hq _ hT).1 ?_, ?_⟩
  · dsimp only
    rw [Category.assoc, hσ, hπ, Category.id_comp]
  · refine (existsUnique_comp_counit_of_isZero Λ i i.openComplement.ι
      i.range_eq_compl_range_openComplement_ι hC ε).unique ?_ (Category.id_comp _)
    rw [Category.assoc]
    exact (congrArg (σ ≫ ·) hπ).trans hσ

variable {i} in
/-- Tensoring on the right with an object `N` with a tensor inverse `N'` preserves the
coreflections into the objects supported on `Z`: every morphism `S ⟶ M ⊗ N` from an object
supported on `Z` factors uniquely through `ε ⊗ N`. -/
lemma bijective_comp_derivedTensorHom_counit
    {N N' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj N).obj N' ≅ 𝟙_ _)
    (e' : ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj N').obj N ≅ 𝟙_ _)
    (M S : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hS : IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj S)) :
    Function.Bijective (fun f : S ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj M))).obj N ↦
      f ≫ derivedTensorHom (ModuleCat.{u + 1} Λ)
        ((rightDerivedUpperShriekAdjunction Λ i).counit.app M) (𝟙 N)) := by
  let E := tensorRightEquivalenceOfTensorIso e e'
  set ε := (rightDerivedUpperShriekAdjunction Λ i).counit.app M
  have hε : derivedTensorHom (ModuleCat.{u + 1} Λ) ε (𝟙 N) = E.functor.map ε := by
    rw [derivedTensorHom_eq_tensorHom, tensorHom_id]
    rfl
  set S' := ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj S).obj N'
  have hS' : IsZero ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).obj S') :=
    isZero_leftDerivedUpperStar_openComplement_derivedTensor (ModuleCat.{u + 1} Λ) i hS N'
  -- `S ≅ F S'` with `F = - ⊗ N`
  let c : E.functor.obj S' ≅ S := E.counitIso.app S
  have hF : Function.Bijective
      (fun f : S' ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj M) ↦ f ≫ ε) :=
    ⟨fun f₁ f₂ hf ↦ (existsUnique_comp_counit_of_isZero Λ i i.openComplement.ι
        i.range_eq_compl_range_openComplement_ι hS' _).unique hf rfl,
      fun g ↦ (existsUnique_comp_counit_of_isZero Λ i i.openComplement.ι
        i.range_eq_compl_range_openComplement_ι hS' g).exists⟩
  have hF' : Function.Bijective (fun f : E.functor.obj S' ⟶
      E.functor.obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj M)) ↦
        f ≫ E.functor.map ε) := by
    constructor
    · intro f₁ f₂ hf
      obtain ⟨g₁, rfl⟩ := E.functor.map_surjective f₁
      obtain ⟨g₂, rfl⟩ := E.functor.map_surjective f₂
      dsimp only at hf
      rw [← Functor.map_comp, ← Functor.map_comp] at hf
      rw [hF.1 (E.functor.map_injective hf)]
    · intro f
      obtain ⟨g, rfl⟩ := E.functor.map_surjective f
      obtain ⟨h, hh⟩ := hF.2 g
      refine ⟨E.functor.map h, ?_⟩
      dsimp only at hh ⊢
      rw [← Functor.map_comp, hh]
  have key : (fun f : S ⟶ ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj M))).obj N ↦
          f ≫ derivedTensorHom (ModuleCat.{u + 1} Λ) ε (𝟙 N)) =
      (fun f ↦ c.inv ≫ f) ∘
        (fun f : E.functor.obj S' ⟶
            E.functor.obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj M)) ↦
          f ≫ E.functor.map ε) ∘ (fun f ↦ c.hom ≫ f) := by
    funext f
    simp only [Function.comp_apply, Category.assoc, Iso.inv_hom_id_assoc, hε]
  rw [key]
  exact (bijective_iso_hom_comp c.symm).comp (hF'.comp (bijective_iso_hom_comp c))

/-- **The product with an invertible coefficient is an isomorphism**: for `N` with a tensor
inverse, `Ri_! Ri^! M ⊗ N ⟶ Ri_! Ri^! (M ⊗ N)` is an isomorphism. -/
theorem isIso_supportedTensorRight
    {N N' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj N).obj N' ≅ 𝟙_ _)
    (e' : ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj N').obj N ≅ 𝟙_ _)
    (M : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (supportedTensorRight Λ i M N) :=
  isIso_of_comp_counit_of_bijective Λ i
    (isZero_leftDerivedUpperStar_openComplement_derivedTensor_rightDerivedLowerShriek
      (ModuleCat.{u + 1} Λ) i _ N) _
    (bijective_comp_derivedTensorHom_counit Λ e e' M) _ (supportedTensorRight_comp_counit Λ i M N)

end TensorRight


section Forget

variable {U Z Z₁ Z' : Scheme.{u}} (i : Z ⟶ U) (i₁ : Z₁ ⟶ U) [IsClosedImmersion i]
  [IsClosedImmersion i₁]

/-- For `Z ⊆ Z₁`, the counit `Ri_! Ri^! L ⟶ L` lifts uniquely through the counit of
`Ri₁_! ⊣ Ri₁^!`. -/
theorem existsUnique_supportedForget (hi : Set.range i.base ⊆ Set.range i₁.base)
    (L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃! κ : (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L) ⟶
        (R(i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(i₁)^![Λ]).obj L),
      κ ≫ (rightDerivedUpperShriekAdjunction Λ i₁).counit.app L =
        (rightDerivedUpperShriekAdjunction Λ i).counit.app L :=
  existsUnique_comp_counit_of_isZero Λ i₁ i₁.openComplement.ι
    i₁.range_eq_compl_range_openComplement_ι
    (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint (ModuleCat.{u + 1} Λ) i _ _
      ((disjoint_range_openComplement_ι i₁).mono_right hi)) _

/-- The *forgetful map* `Ri_! Ri^! L ⟶ Ri₁_! Ri₁^! L` for `Z ⊆ Z₁`, forgetting that a class is
supported on the smaller closed subset: the unique lift of the counit of `Ri_! ⊣ Ri^!` through
that of `Ri₁_! ⊣ Ri₁^!`. -/
noncomputable def supportedForget (hi : Set.range i.base ⊆ Set.range i₁.base)
    (L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L) ⟶
      (R(i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(i₁)^![Λ]).obj L) :=
  (existsUnique_supportedForget Λ i i₁ hi L).exists.choose

/-- The defining property of `AlgebraicGeometry.Etale.supportedForget`. -/
@[reassoc]
lemma supportedForget_comp_counit (hi : Set.range i.base ⊆ Set.range i₁.base)
    (L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    supportedForget Λ i i₁ hi L ≫ (rightDerivedUpperShriekAdjunction Λ i₁).counit.app L =
      (rightDerivedUpperShriekAdjunction Λ i).counit.app L :=
  (existsUnique_supportedForget Λ i i₁ hi L).exists.choose_spec

variable (j : Z' ⟶ Z₁) [IsClosedImmersion j]

/-- For `Z ⊆ Z₁` and a closed immersion `j : Z' ⟶ Z₁` whose open complement maps into the open
complement of `Z`, the pullback `Li₁^* κ` of the forgetful map lifts uniquely through the counit
of `Rj_! ⊣ Rj^!`. -/
theorem existsUnique_supportedPullbackForget (hi : Set.range i.base ⊆ Set.range i₁.base)
    (hd : Disjoint (Set.range (j.openComplement.ι ≫ i₁).base) (Set.range i.base))
    (L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃! ω : (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) ⟶
        (R(j)_![ModuleCat.{u + 1} Λ]).obj ((R(j)^![Λ]).obj
          ((L((i₁)^*[ModuleCat.{u + 1} Λ])).obj
            ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(i₁)^![Λ]).obj L)))),
      ω ≫ (rightDerivedUpperShriekAdjunction Λ j).counit.app _ =
        (L((i₁)^*[ModuleCat.{u + 1} Λ])).map (supportedForget Λ i i₁ hi L) :=
  existsUnique_comp_counit_of_isZero Λ j j.openComplement.ι
    j.range_eq_compl_range_openComplement_ι
    (isZero_leftDerivedUpperStar_openComplement_leftDerivedUpperStar_of_disjoint
      (ModuleCat.{u + 1} Λ) i₁ i j hd _) _

/-- The restriction to `Z₁` of the forgetful map `Ri_! Ri^! L ⟶ Ri₁_! Ri₁^! L`, read as a class
supported on `Z'`: the map `Li₁^* Ri_! Ri^! L ⟶ Rj_! Rj^! (Li₁^* Ri₁_! Ri₁^! L)` lifting
`Li₁^* κ` through the counit of `Rj_! ⊣ Rj^!`. -/
noncomputable def supportedPullbackForget (hi : Set.range i.base ⊆ Set.range i₁.base)
    (hd : Disjoint (Set.range (j.openComplement.ι ≫ i₁).base) (Set.range i.base))
    (L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) ⟶
      (R(j)_![ModuleCat.{u + 1} Λ]).obj ((R(j)^![Λ]).obj
        ((L((i₁)^*[ModuleCat.{u + 1} Λ])).obj
          ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(i₁)^![Λ]).obj L)))) :=
  (existsUnique_supportedPullbackForget Λ i i₁ j hi hd L).exists.choose

/-- The defining property of `AlgebraicGeometry.Etale.supportedPullbackForget`. -/
@[reassoc]
lemma supportedPullbackForget_comp_counit (hi : Set.range i.base ⊆ Set.range i₁.base)
    (hd : Disjoint (Set.range (j.openComplement.ι ≫ i₁).base) (Set.range i.base))
    (L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    supportedPullbackForget Λ i i₁ j hi hd L ≫
        (rightDerivedUpperShriekAdjunction Λ j).counit.app _ =
      (L((i₁)^*[ModuleCat.{u + 1} Λ])).map (supportedForget Λ i i₁ hi L) :=
  (existsUnique_supportedPullbackForget Λ i i₁ j hi hd L).exists.choose_spec

end Forget

section Product

variable {A} in
/-- Naturality of the inverse of the left unitor of the derived tensor product. -/
@[reassoc]
lemma derivedTensorLeftUnitor_inv_comp_derivedTensorHom_id {X : Scheme.{u}}
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : M ⟶ M') :
    (derivedTensorLeftUnitor A X M).inv ≫ derivedTensorHom A (𝟙 (𝟙_ _)) f =
      f ≫ (derivedTensorLeftUnitor A X M').inv := by
  rw [Iso.inv_comp_eq, ← derivedTensorHom_id_comp_derivedTensorLeftUnitor_hom_assoc,
    Iso.hom_inv_id, Category.comp_id]

variable {U Z₁ Z₂ Z Z' : Scheme.{u}} (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
  (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)

/-- Forgetting the support of a cup product down to `Z₁`: the product of supports followed by the
forgetful map `Ri_! Ri^! ⟶ Ri₁_! Ri₁^!` is `1 ⊗ ε₂` followed by the product with coefficients. -/
theorem supportedProduct_comp_supportedForget
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    supportedProduct Λ i₁ i₂ i h M N ≫
        supportedForget Λ i i₁ (h ▸ Set.inter_subset_left)
          (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj M).obj N) =
      derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 _)
          ((rightDerivedUpperShriekAdjunction Λ i₂).counit.app N) ≫
        supportedTensorRight Λ i₁ M N :=
  (existsUnique_comp_counit_of_isZero Λ i₁ i₁.openComplement.ι
    i₁.range_eq_compl_range_openComplement_ι
    (isZero_leftDerivedUpperStar_openComplement_derivedTensor_rightDerivedLowerShriek
      (ModuleCat.{u + 1} Λ) i₁ _ _)
    (L := ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj M).obj N)
    (derivedTensorHom (ModuleCat.{u + 1} Λ)
      ((rightDerivedUpperShriekAdjunction Λ i₁).counit.app M)
      ((rightDerivedUpperShriekAdjunction Λ i₂).counit.app N))).unique
    (by rw [Category.assoc, supportedForget_comp_counit, supportedProduct_comp_counit])
    (by
      rw [Category.assoc, supportedTensorRight_comp_counit, derivedTensorHom_comp,
        Category.id_comp]
      exact congrArg (derivedTensorHom (ModuleCat.{u + 1} Λ) _) (Category.comp_id _))

/-- The map `Ri₂_! Ri₂^! N ≅ 𝟙 ⊗ Ri₂_! Ri₂^! N ⟶ Ri₁_! Ri₁^! M ⊗ Ri₂_! Ri₂^! N ⟶ Ri_! Ri^! (M ⊗ N)`
through which the cup product `α ∪ β` factors, followed by the forgetful map to `Z₁`, is the
counit `ε₂` followed by `N ≅ 𝟙 ⊗ N ⟶ Ri₁_! Ri₁^! M ⊗ N ⟶ Ri₁_! Ri₁^! (M ⊗ N)`. -/
theorem supportedProduct_comp_supportedForget_eq
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (α : 𝟙_ _ ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(i₁)^![Λ]).obj M)) :
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U _).inv ≫
        derivedTensorHom (ModuleCat.{u + 1} Λ) α (𝟙 _) ≫
        supportedProduct Λ i₁ i₂ i h M N ≫
          supportedForget Λ i i₁ (h ▸ Set.inter_subset_left)
            (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj M).obj N) =
      (rightDerivedUpperShriekAdjunction Λ i₂).counit.app N ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U N).inv ≫
          derivedTensorHom (ModuleCat.{u + 1} Λ) α (𝟙 N) ≫
          supportedTensorRight Λ i₁ M N := by
  have e : derivedTensorHom (ModuleCat.{u + 1} Λ) α
        (𝟙 ((R(i₂)_![ModuleCat.{u + 1} Λ]).obj ((R(i₂)^![Λ]).obj N))) ≫
      derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 _)
        ((rightDerivedUpperShriekAdjunction Λ i₂).counit.app N) =
        derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 (𝟙_ _))
            ((rightDerivedUpperShriekAdjunction Λ i₂).counit.app N) ≫
          derivedTensorHom (ModuleCat.{u + 1} Λ) α (𝟙 N) := by
    rw [derivedTensorHom_comp, derivedTensorHom_comp]
    simp only [Category.id_comp, Category.comp_id]
    exact congrArg (derivedTensorHom (ModuleCat.{u + 1} Λ) α) (Category.comp_id _).symm
  rw [supportedProduct_comp_supportedForget, reassoc_of% e,
    derivedTensorLeftUnitor_inv_comp_derivedTensorHom_id_assoc]

variable (j : Z' ⟶ Z₁) (g : Z' ⟶ Z₂) [IsClosedImmersion j]
  (hg : IsPullback g j i₂ i₁)

/-- **The restriction of a cup product to `Z₁`.** Let `Z' = Z₁ ×_U Z₂` with `j : Z' ⟶ Z₁`, let
`Z = Z₁ ∩ Z₂`, `α : 𝟙 ⟶ Ri₁_! Ri₁^! M` and `τ : Li₁^* N ≅ L'`. Write
`Q : Ri₂_! Ri₂^! N ⟶ Ri_! Ri^! (M ⊗ N)` for the map through which `α ∪ -` factors and
`αN : N ⟶ Ri₁_! Ri₁^! (M ⊗ N)` for the product of `α` with `N`. Then, through the restriction
`ω` of the forgetful map (`AlgebraicGeometry.Etale.supportedPullbackForget`),

`Li₁^* Q ≫ ω = ψ ≫ Rj_! Rj^! (τ⁻¹ ≫ Li₁^* αN)`,

where `ψ : Li₁^* Ri₂_! Ri₂^! N ⟶ Rj_! Rj^! L'` is the restriction of supports along `i₁`. -/
theorem leftDerivedUpperStar_map_supportedProduct_comp
    (M N : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L' : DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (τ : (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj N ≅ L')
    (α : 𝟙_ _ ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj ((R(i₁)^![Λ]).obj M)) :
    (L((i₁)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U _).inv ≫
          derivedTensorHom (ModuleCat.{u + 1} Λ) α (𝟙 _) ≫
          supportedProduct Λ i₁ i₂ i h M N) ≫
        supportedPullbackForget Λ i i₁ j (h ▸ Set.inter_subset_left)
          (disjoint_range_openComplement_ι_comp_of_isPullback_of_subset hg
            (h ▸ Set.inter_subset_right)) _ =
      supportedRestriction Λ i₁ i₂ j g hg N L' τ ≫
        (R(j)_![ModuleCat.{u + 1} Λ]).map ((R(j)^![Λ]).map
          (τ.inv ≫ (L((i₁)^*[ModuleCat.{u + 1} Λ])).map
            ((derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U N).inv ≫
              derivedTensorHom (ModuleCat.{u + 1} Λ) α (𝟙 N) ≫
              supportedTensorRight Λ i₁ M N))) := by
  have hψ : supportedRestriction Λ i₁ i₂ j g hg N L' τ ≫
      (rightDerivedUpperShriekAdjunction Λ j).counit.app L' =
        (L((i₁)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekAdjunction Λ i₂).counit.app N) ≫ τ.hom :=
    (existsUnique_supportedRestriction Λ i₁ i₂ j g hg N L' τ).exists.choose_spec
  refine (existsUnique_comp_counit_of_isZero Λ j j.openComplement.ι
    j.range_eq_compl_range_openComplement_ι
    (isZero_leftDerivedUpperStar_openComplement_leftDerivedUpperStar_of_disjoint
      (ModuleCat.{u + 1} Λ) i₁ i₂ j (disjoint_range_openComplement_ι_comp_of_isPullback hg) _)
    (L := (L((i₁)^*[ModuleCat.{u + 1} Λ])).obj
      ((R(i₁)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i₁)^![Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj M).obj N))))
    ((L((i₁)^*[ModuleCat.{u + 1} Λ])).map
      ((rightDerivedUpperShriekAdjunction Λ i₂).counit.app N ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U N).inv ≫
        derivedTensorHom (ModuleCat.{u + 1} Λ) α (𝟙 N) ≫
        supportedTensorRight Λ i₁ M N))).unique ?_ ?_
  · rw [Category.assoc, supportedPullbackForget_comp_counit, ← Functor.map_comp,
      Category.assoc, Category.assoc, supportedProduct_comp_supportedForget_eq]
  · rw [Category.assoc]
    erw [(rightDerivedUpperShriekAdjunction Λ j).counit.naturality]
    rw [Functor.id_map, reassoc_of% hψ, Iso.hom_inv_id_assoc, ← Functor.map_comp]

end Product

end Etale

end AlgebraicGeometry
