/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.ConstructibleSheaf.DerivedMorphismDescentShift
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.Concentrated
public import WeilConjectures.SixFunctors.Etale.Derived.InvertiblePullback
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekInvertible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Gluing comparisons along the affine line

The inputs of the gluing half of blueprint `lemma-section-normal-bundle--1`
(`AlgebraicGeometry.Etale.existsUnique_iso_leftDerivedUpperStar_of_etale`):

* the unit section of `𝔸¹_S` is a closed immersion meeting every fibre, and the affine line
  commutes with fibre products;
* a shift and twist of a lisse rank-one sheaf is invertible, and is a sheaf placed in one
  degree (`AlgebraicGeometry.Etale.exists_iso_tateTwist_singleFunctor_obj`);
* *agreement on overlaps*: two comparisons normalized at the unit section have the same
  restriction to the overlap of an étale cover, comparisons out of an invertible object being
  determined at the unit section
  (`AlgebraicGeometry.Etale.conj_leftDerivedUpperStar_eq_of_section`);
* *gluing*: an isomorphism between pullbacks of invertible objects concentrated in one degree
  whose two restrictions to the overlap agree descends
  (`AlgebraicGeometry.Etale.exists_iso_leftDerivedUpperStar_map_hom_eq_of_isPullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The unit section `t = 1` of `𝔸¹_S ⟶ S` is a closed immersion, being a section of a separated
morphism. -/
lemma isClosedImmersion_oneSection (S : Scheme.{u}) :
    IsClosedImmersion (AffineSpace.oneSection (ULift.{u} (Fin 1)) S) := by
  have : IsClosedImmersion
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S ≫ 𝔸(ULift.{u} (Fin 1); S) ↘ S) := by
    rw [AffineSpace.oneSection_comp_over]
    infer_instance
  exact IsClosedImmersion.of_comp _ (𝔸(ULift.{u} (Fin 1); S) ↘ S)

/-- Every point of `𝔸¹_S` lies in a preconnected set meeting the unit section: its fibre over
`S`, which is irreducible. -/
lemma exists_isPreconnected_inter_range_oneSection (S : Scheme.{u})
    (x : 𝔸(ULift.{u} (Fin 1); S)) :
    ∃ T : Set 𝔸(ULift.{u} (Fin 1); S), _root_.IsPreconnected T ∧ x ∈ T ∧
      (T ∩ Set.range (AffineSpace.oneSection (ULift.{u} (Fin 1)) S).base).Nonempty := by
  let π := 𝔸(ULift.{u} (Fin 1); S) ↘ S
  let i₁ := AffineSpace.oneSection (ULift.{u} (Fin 1)) S
  have hp : i₁ ≫ π = 𝟙 S := AffineSpace.oneSection_comp_over _ _
  exact ⟨π.base ⁻¹' {π.base x}, (π.isIrreducible_preimage
      (AffineSpace.isOpenMap_over (n := ULift.{u} (Fin 1)) S)
      isIrreducible_singleton).isPreirreducible.isPreconnected, rfl, i₁.base (π.base x),
      by simpa using congrArg (fun f : S ⟶ S ↦ f.base (π.base x)) hp, π.base x, rfl⟩

/-- The affine line commutes with fibre products: `𝔸¹_{Y' ×_Y Y'} = 𝔸¹_{Y'} ×_{𝔸¹_Y} 𝔸¹_{Y'}`. -/
lemma isPullback_affineSpace_map {Y Y' Y'' : Scheme.{u}} {v : Y' ⟶ Y} {p₁ p₂ : Y'' ⟶ Y'}
    (h : IsPullback p₁ p₂ v v) :
    IsPullback (AffineSpace.map (ULift.{u} (Fin 1)) p₁) (AffineSpace.map (ULift.{u} (Fin 1)) p₂)
      (AffineSpace.map (ULift.{u} (Fin 1)) v) (AffineSpace.map (ULift.{u} (Fin 1)) v) := by
  refine IsPullback.flip (IsPullback.of_right ?_ ?_ (AffineSpace.isPullback_map v).flip)
  · rw [AffineSpace.map_over, AffineSpace.map_over]
    exact (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) p₁).flip.paste_horiz h.flip
  · rw [← AffineSpace.map_comp, ← AffineSpace.map_comp, h.w]

/-- A lisse rank-one sheaf `L`, twisted, is a sheaf placed in degree zero: with
`Λ(m) ≅ T[0]` for a lisse rank-one `T`, the derived tensor product `L[0] ⊗ᴸ T[0]` is
`(L ⊗ T)[0]`, `L` being flat. -/
lemma exists_iso_tateTwist_singleFunctor_obj [HasTateTwist Λ] {X : Scheme.{u}}
    [HasInvertibleExponent Λ X] (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf L]
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) (m : ℤ) :
    ∃ S : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Nonempty ((tateTwist Λ X m).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj S) := by
  obtain ⟨T, -, -, ⟨eT⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) X m
  exact ⟨L ⊗ T, ⟨((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L)).mapIso eT ≪≫
    singleFunctorObjTensorIso L T
      (ObjectProperty.flat_of_tensorIso (tensorIhomUnitIsoOfIsLocallyConstantSheaf L hL))⟩⟩

/-- A lisse rank-one sheaf `L`, twisted, is invertible. -/
lemma isInvertible_tateTwist_singleFunctor_obj [HasTateTwist Λ] {X : Scheme.{u}}
    [HasInvertibleExponent Λ X] (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf L]
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) (m : ℤ) :
    DerivedCategory.isInvertible Λ X
      ((tateTwist Λ X m).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) :=
  DerivedCategory.isInvertible.derivedTensor
    ((isInvertible_iff_exists_derivedTensor _).1
      (isInvertible_singleFunctor_obj_of_isLocallyConstantSheaf L hL))
    (isInvertible_tateObject Λ X m)

/-- An object which becomes, after pullback along a surjective étale `u`, a shift and twist of a
lisse rank-one sheaf is invertible: invertibility descends along `u`
(`AlgebraicGeometry.Etale.isInvertible_of_isInvertible_leftDerivedUpperStar_of_etale`). -/
lemma isInvertible_of_leftDerivedUpperStar_iso_tateTwist [Finite Λ] [HasTateTwist Λ]
    {U T : Scheme.{u}} (u : U ⟶ T) [Etale u] [Surjective u] [HasInvertibleExponent Λ U]
    {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (L : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf L]
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) (m n : ℤ)
    (e : (L((u)^*[ModuleCat.{u + 1} Λ])).obj K ≅
      ((tateTwist Λ U m).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj L))⟦n⟧) :
    DerivedCategory.isInvertible Λ T K :=
  isInvertible_of_isInvertible_leftDerivedUpperStar_of_etale u
    (((isInvertible_tateTwist_singleFunctor_obj L hL m).shift n).of_iso e.symm)

/-- If `Lu^* K` is a sheaf placed in one degree `-n`, for a surjective étale `u`, then so is `K`:
the shift `K⟦-n⟧` is a sheaf placed in degree zero
(`lem-pur-concentrated-complex-shift`). -/
lemma exists_iso_shift_singleFunctor_obj_of_leftDerivedUpperStar_iso {U T : Scheme.{u}}
    (u : U ⟶ T) [Etale u] [Surjective u]
    {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {S : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (n : ℤ)
    (e : (L((u)^*[ModuleCat.{u + 1} Λ])).obj K ≅
      ((_root_.DerivedCategory.singleFunctor _ 0).obj S)⟦n⟧) :
    ∃ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Nonempty (K⟦-n⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
  let e₀ : (L((u)^*[ModuleCat.{u + 1} Λ])).obj (K⟦-n⟧) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj S :=
    ((L((u)^*[ModuleCat.{u + 1} Λ])).commShiftIso (-n)).app K ≪≫
      (shiftFunctor _ (-n)).mapIso e ≪≫ (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).app _
  obtain ⟨c⟩ := _root_.DerivedCategory.nonempty_iso_singleFunctor_obj_homologyFunctor_obj
    (K⟦-n⟧) 0 (isZero_homology_of_leftDerivedUpperStar_iso Λ u e₀)
  exact ⟨_, ⟨c⟩⟩

/-- **Gluing isomorphisms along a surjective étale morphism.** Let `u : U ⟶ T` be surjective and
étale, `Z = U ×_T U`, and `K, M ∈ D(T_ét, Λ)` invertible with `K⟦n⟧, M⟦n⟧` sheaves placed in
degree zero. An isomorphism `δ : Lu^* K ≅ Lu^* M` whose two pullbacks to `Z` agree is `Lu^* κ`
for an isomorphism `κ : K ≅ M`. -/
theorem exists_iso_leftDerivedUpperStar_map_hom_eq_of_isPullback {T U Z : Scheme.{u}}
    {K M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.isInvertible Λ T K) (hM : DerivedCategory.isInvertible Λ T M)
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (n : ℤ)
    (eK : K⟦n⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj F)
    (eM : M⟦n⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj G)
    (u : U ⟶ T) [Etale u] [Surjective u] {r₁ r₂ : Z ⟶ U} (hZ : IsPullback r₁ r₂ u u)
    (δ : (L((u)^*[ModuleCat.{u + 1} Λ])).obj K ≅ (L((u)^*[ModuleCat.{u + 1} Λ])).obj M)
    (hδ : (leftDerivedUpperStarComp _ r₁ u).hom.app K ≫ (L((r₁)^*[_])).map δ.hom ≫
          (leftDerivedUpperStarComp _ r₁ u).inv.app M =
        (leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w).hom.app K ≫ (L((r₂)^*[_])).map δ.hom ≫
          (leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w).inv.app M) :
    ∃ κ : K ≅ M, (L((u)^*[ModuleCat.{u + 1} Λ])).map κ.hom = δ.hom := by
  have hY : (leftDerivedUpperStarComp _ r₁ u).app K ≪≫ (L((r₁)^*[_])).mapIso δ ≪≫
        ((leftDerivedUpperStarComp _ r₁ u).app M).symm =
      (leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w).app K ≪≫ (L((r₂)^*[_])).mapIso δ ≪≫
        ((leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w).app M).symm := by
    ext
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom]
      using hδ
  have hδ' := congrArg Iso.inv hY
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv,
    Category.assoc] at hδ'
  obtain ⟨γ, hγ⟩ := exists_leftDerivedUpperStar_map_eq_of_isPullback_of_shift n eK eM u hZ
    δ.hom hδ
  obtain ⟨γ', hγ'⟩ := exists_leftDerivedUpperStar_map_eq_of_isPullback_of_shift n eM eK u hZ
    δ.inv hδ'
  refine ⟨⟨γ, γ', ?_, ?_⟩, hγ⟩
  · exact eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible_of_surjective u hK _
      (by rw [Functor.map_comp, hγ, hγ', δ.hom_inv_id])
  · exact eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible_of_surjective u hM _
      (by rw [Functor.map_comp, hγ, hγ', δ.inv_hom_id])

/-- Let `i : Z ⟶ X` be a closed immersion such that every point of `X` lies in a preconnected set
meeting `i`. Two morphisms `f, g : F ⟶ G` out of an invertible `F`, with `g` an isomorphism,
which agree after `Li^*` are equal: `f ≫ g⁻¹` is an endomorphism of `F` restricting to the
identity (`AlgebraicGeometry.Etale.eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible`). -/
lemma eq_of_leftDerivedUpperStar_map_eq_of_isInvertible {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (hi : ∀ x : X, ∃ S : Set X, _root_.IsPreconnected S ∧ x ∈ S ∧
      (S ∩ Set.range i.base).Nonempty)
    {F G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hF : DerivedCategory.isInvertible Λ X F) (f g : F ⟶ G) [IsIso g]
    (h : (L((i)^*[ModuleCat.{u + 1} Λ])).map f = (L((i)^*[ModuleCat.{u + 1} Λ])).map g) :
    f = g := by
  have h' := eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible i hi hF
    (f ≫ inv g) (by rw [Functor.map_comp, Functor.map_inv, h, IsIso.hom_inv_id])
  rw [← Category.comp_id f, ← IsIso.inv_hom_id g, ← Category.assoc, h', Category.id_comp]

/-- Two morphisms `f, g : F ⟶ G` out of an invertible `F`, with `g` an isomorphism, which agree
after pullback along a surjective `π` are equal
(`AlgebraicGeometry.Etale.eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible_of_surjective`).
-/
lemma eq_of_leftDerivedUpperStar_map_eq_of_isInvertible_of_surjective {X Z : Scheme.{u}}
    (π : Z ⟶ X) [Surjective π]
    {F G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hF : DerivedCategory.isInvertible Λ X F) (f g : F ⟶ G) [IsIso g]
    (h : (L((π)^*[ModuleCat.{u + 1} Λ])).map f = (L((π)^*[ModuleCat.{u + 1} Λ])).map g) :
    f = g := by
  have h' := eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible_of_surjective π hF
    (f ≫ inv g) (by rw [Functor.map_comp, Functor.map_inv, h, IsIso.hom_inv_id])
  rw [← Category.comp_id f, ← IsIso.inv_hom_id g, ← Category.assoc, h', Category.id_comp]

/-- **The local comparison at the unit section.** Let `a : P ⟶ B` with section `i`,
`a' : P' ⟶ B'` with section `i'`, and `w : P' ⟶ P` over `v : B' ⟶ B` carrying `i'` to `i`. Let
`θ : Li^* F ≅ C` and let `κ' : Lw^* F ≅ La'^* Lv^* C` be normalized at `i'` against `θ`. Then
`κ'`, viewed as a map `Lw^* F ⟶ Lw^* La^* C` and restricted along `i'`, is the pullback along
`v` of `θ`, viewed as a map `Li^* F ⟶ Li^* La^* C`, through `L(i' ≫ w)^* = L(v ≫ i)^*`. -/
theorem conj_leftDerivedUpperStar_section_eq {B B' P P' : Scheme.{u}}
    {a : P ⟶ B} {a' : P' ⟶ B'} {v : B' ⟶ B} {w : P' ⟶ P} {i : B ⟶ P} {i' : B' ⟶ P'}
    (hw : w ≫ a = a' ≫ v) (h : i ≫ a = 𝟙 B) (h' : i' ≫ a' = 𝟙 B') (hi : i' ≫ w = v ≫ i)
    {F : _root_.DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {C : _root_.DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (θ : (L((i)^*[ModuleCat.{u + 1} Λ])).obj F ≅ C)
    (κ' : (L((w)^*[ModuleCat.{u + 1} Λ])).obj F ≅
      (L((a')^*[ModuleCat.{u + 1} Λ])).obj ((L((v)^*[ModuleCat.{u + 1} Λ])).obj C))
    (hκ' : (L((i')^*[ModuleCat.{u + 1} Λ])).map κ'.hom ≫
          (leftDerivedUpperStarCompSectionIso _ i' a' h').hom.app _ =
        ((leftDerivedUpperStarComp _ i' w).inv.app F ≫
          (leftDerivedUpperStarComp _ v i _ hi).hom.app F) ≫
        (L((v)^*[ModuleCat.{u + 1} Λ])).map θ.hom) :
    (leftDerivedUpperStarComp _ i' w).hom.app F ≫
        (L((i')^*[ModuleCat.{u + 1} Λ])).map (κ'.hom ≫
          (leftDerivedUpperStarComp _ a' v _ hw).inv.app C ≫
          (leftDerivedUpperStarComp _ w a).hom.app C) ≫
        (leftDerivedUpperStarComp _ i' w).inv.app _ =
      (leftDerivedUpperStarComp _ v i _ hi).hom.app F ≫
        (L((v)^*[ModuleCat.{u + 1} Λ])).map (θ.hom ≫
          (leftDerivedUpperStarCompSectionIso _ i a h).inv.app C) ≫
        (leftDerivedUpperStarComp _ v i _ hi).inv.app _ := by
  -- the restriction of `κ'` at `i'`, read through `θ`
  have hκ'' : (L((i')^*[ModuleCat.{u + 1} Λ])).map κ'.hom =
      (leftDerivedUpperStarComp _ i' w).inv.app F ≫
        (leftDerivedUpperStarComp _ v i _ hi).hom.app F ≫
        (L((v)^*[ModuleCat.{u + 1} Λ])).map θ.hom ≫
        (leftDerivedUpperStarCompSectionIso _ i' a' h').inv.app _ := by
    have := hκ' =≫ (leftDerivedUpperStarCompSectionIso _ i' a' h').inv.app
      ((L((v)^*[ModuleCat.{u + 1} Λ])).obj C)
    simp only [Category.assoc, Iso.hom_inv_id_app] at this
    erw [Category.comp_id] at this
    exact this
  -- sections commute with base change
  have H := leftDerivedUpperStar_map_comp_compSectionIso (ModuleCat.{u + 1} Λ) v a a' w i i'
    hw hi h h' C
  have H' : (L((i')^*[ModuleCat.{u + 1} Λ])).mapIso
        (((leftDerivedUpperStarComp _ w a).app C).symm ≪≫
          (leftDerivedUpperStarComp _ a' v _ hw).app C) ≪≫
        (leftDerivedUpperStarCompSectionIso _ i' a' h').app _ =
      ((leftDerivedUpperStarComp _ i' w).app _).symm ≪≫
        (leftDerivedUpperStarComp _ v i _ hi).app _ ≪≫
        (L((v)^*[ModuleCat.{u + 1} Λ])).mapIso
          ((leftDerivedUpperStarCompSectionIso _ i a h).app C) := by
    ext
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
      Category.assoc] using H
  have H'' := congrArg Iso.inv H'
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv,
    Category.assoc, Functor.map_comp] at H''
  rw [Functor.map_comp, Functor.map_comp, hκ'']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% H'']
  simp [Functor.map_comp]

-- the comparison manipulates long composites of derived pullback isomorphisms
/-- **Agreement on overlaps.** Let `a : P ⟶ B` with section `i`, `a' : P' ⟶ B'` with section
`i'`, and `w : P' ⟶ P` over `v : B' ⟶ B` carrying `i'` to `i`; let `r₁, r₂ : P'' ⟶ P'` lie over
`p₁, p₂ : B'' ⟶ B'` with `p₁ ≫ v = p₂ ≫ v`, carrying a section `i''` to `i'`, and suppose every
point of `P''` lies in a preconnected set meeting the closed immersion `i''`. Let `F ∈ D(P)` be
invertible, `θ : Li^* F ≅ C`, and `κ' : Lw^* F ≅ La'^* Lv^* C` normalized at `i'` against `θ`.
Then the two pullbacks of `κ'`, viewed as maps `Lw^* F ⟶ Lw^* La^* C`, to `P''` agree: both are
normalized at `i''` against the pullback of `θ`, and comparisons out of an invertible object
are determined at `i''`
(`AlgebraicGeometry.Etale.eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible`). -/
theorem conj_leftDerivedUpperStar_eq_of_section {B B' B'' P P' P'' : Scheme.{u}}
    {a : P ⟶ B} {a' : P' ⟶ B'} {v : B' ⟶ B} {w : P' ⟶ P} {p₁ p₂ : B'' ⟶ B'}
    {r₁ r₂ : P'' ⟶ P'} {i : B ⟶ P} {i' : B' ⟶ P'} {i'' : B'' ⟶ P''} [IsClosedImmersion i'']
    (hi'' : ∀ x : P'', ∃ S : Set P'', _root_.IsPreconnected S ∧ x ∈ S ∧
      (S ∩ Set.range i''.base).Nonempty)
    (hw : w ≫ a = a' ≫ v) (h : i ≫ a = 𝟙 B) (h' : i' ≫ a' = 𝟙 B') (hi : i' ≫ w = v ≫ i)
    (hr₁ : i'' ≫ r₁ = p₁ ≫ i') (hr₂ : i'' ≫ r₂ = p₂ ≫ i') (hp : p₁ ≫ v = p₂ ≫ v)
    (hr : r₁ ≫ w = r₂ ≫ w)
    {F : _root_.DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hF : DerivedCategory.isInvertible Λ P F)
    {C : _root_.DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (θ : (L((i)^*[ModuleCat.{u + 1} Λ])).obj F ≅ C)
    (κ' : (L((w)^*[ModuleCat.{u + 1} Λ])).obj F ≅
      (L((a')^*[ModuleCat.{u + 1} Λ])).obj ((L((v)^*[ModuleCat.{u + 1} Λ])).obj C))
    (hκ' : (L((i')^*[ModuleCat.{u + 1} Λ])).map κ'.hom ≫
          (leftDerivedUpperStarCompSectionIso _ i' a' h').hom.app _ =
        ((leftDerivedUpperStarComp _ i' w).inv.app F ≫
          (leftDerivedUpperStarComp _ v i _ hi).hom.app F) ≫
        (L((v)^*[ModuleCat.{u + 1} Λ])).map θ.hom) :
    (leftDerivedUpperStarComp _ r₁ w).hom.app F ≫
        (L((r₁)^*[ModuleCat.{u + 1} Λ])).map (κ'.hom ≫
          (leftDerivedUpperStarComp _ a' v _ hw).inv.app C ≫
          (leftDerivedUpperStarComp _ w a).hom.app C) ≫
        (leftDerivedUpperStarComp _ r₁ w).inv.app _ =
      (leftDerivedUpperStarComp _ r₂ w (r₁ ≫ w) hr).hom.app F ≫
        (L((r₂)^*[ModuleCat.{u + 1} Λ])).map (κ'.hom ≫
          (leftDerivedUpperStarComp _ a' v _ hw).inv.app C ≫
          (leftDerivedUpperStarComp _ w a).hom.app C) ≫
        (leftDerivedUpperStarComp _ r₂ w (r₁ ≫ w) hr).inv.app _ := by
  have hD := conj_leftDerivedUpperStar_section_eq hw h h' hi θ κ' hκ'
  -- both restrictions to `P''`, read at `i''`, are the pullback of `θ` to `B''`
  have key (p : B'' ⟶ B') (r : P'' ⟶ P') (hr' : i'' ≫ r = p ≫ i') (hrw : r₁ ≫ w = r ≫ w)
      (hpv : p₁ ≫ v = p ≫ v) :
      (leftDerivedUpperStarComp _ i'' (r₁ ≫ w)).hom.app F ≫
          (L((i'')^*[ModuleCat.{u + 1} Λ])).map
            ((leftDerivedUpperStarComp _ r w (r₁ ≫ w) hrw).hom.app F ≫
              (L((r)^*[ModuleCat.{u + 1} Λ])).map (κ'.hom ≫
                (leftDerivedUpperStarComp _ a' v _ hw).inv.app C ≫
                (leftDerivedUpperStarComp _ w a).hom.app C) ≫
              (leftDerivedUpperStarComp _ r w (r₁ ≫ w) hrw).inv.app _) ≫
          (leftDerivedUpperStarComp _ i'' (r₁ ≫ w)).inv.app _ =
        (leftDerivedUpperStarComp _ (p₁ ≫ v) i (i'' ≫ r₁ ≫ w)
            (by rw [reassoc_of% hr₁, hi, Category.assoc])).hom.app F ≫
          (L((p₁ ≫ v)^*[ModuleCat.{u + 1} Λ])).map (θ.hom ≫
            (leftDerivedUpperStarCompSectionIso _ i a h).inv.app C) ≫
          (leftDerivedUpperStarComp _ (p₁ ≫ v) i (i'' ≫ r₁ ≫ w)
            (by rw [reassoc_of% hr₁, hi, Category.assoc])).inv.app _ := by
    have e : i'' ≫ r₁ ≫ w = (p ≫ i') ≫ w := by rw [hrw, ← Category.assoc, hr']
    have T₁ := Etale.leftDerivedUpperStarComp_conj_comp i'' r w (p ≫ i') (r₁ ≫ w)
      (i'' ≫ r₁ ≫ w) hr'.symm hrw e (κ'.hom ≫
        (leftDerivedUpperStarComp _ a' v _ hw).inv.app C ≫
        (leftDerivedUpperStarComp _ w a).hom.app C)
    have T₂ := Etale.leftDerivedUpperStarComp_conj_comp p i' w (p ≫ i') (i' ≫ w)
      (i'' ≫ r₁ ≫ w) rfl rfl e (κ'.hom ≫
        (leftDerivedUpperStarComp _ a' v _ hw).inv.app C ≫
        (leftDerivedUpperStarComp _ w a).hom.app C)
    have T₃ := Etale.leftDerivedUpperStarComp_conj_comp p v i (p₁ ≫ v) (i' ≫ w)
      (i'' ≫ r₁ ≫ w) hpv hi (by rw [reassoc_of% hr₁, hi, Category.assoc]) (θ.hom ≫
        (leftDerivedUpperStarCompSectionIso _ i a h).inv.app C)
    rw [← T₁]
    rw [T₂]
    rw [hD]
    rw [← T₃]
  have k₁ := key p₁ r₁ hr₁ rfl rfl
  have k₂ := key p₂ r₂ hr₂ hr hp
  rw [← k₂] at k₁
  exact eq_of_leftDerivedUpperStar_map_eq_of_isInvertible i'' hi''
    (hF.leftDerivedUpperStar (r₁ ≫ w)) _ _ ((cancel_mono _).1 ((cancel_epi _).1 k₁))

end Etale

end AlgebraicGeometry
