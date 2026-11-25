/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Affine.EtaleAffineLinePullbackFull
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-! # Existence of normalized shifted-line comparisons

This is the existence part of the gluing argument in the blueprint, separated from
rigidity and independence of comparisons. Affine-line fullness makes this existence
result valid for arbitrary sheaves placed in a common degree and arbitrary rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

namespace AlgebraicGeometry.Etale

private theorem line_pullback_faithful (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).Faithful := by
  exact Functor.Faithful.of_comp_iso
    ((upperStarComp (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) (𝟙 S)
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S).symm).symm ≪≫
        upperStarId (ModuleCat.{u + 1} A) S)

-- The mate identity compares large composites of sheaf inverse images.
private theorem line_counit_isIso (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    (P : Sheaf (AffineSpace (ULift.{u} (Fin 1)) S).smallEtaleTopology
      (ModuleCat.{u + 1} A))
    (cover : Scheme.Cover.{u} Scheme.etalePrecoverage S)
    (hloc : ∀ j : cover.I₀, ∃ Q : Sheaf (cover.X j).smallEtaleTopology
      (ModuleCat.{u + 1} A), Nonempty
      ((upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))).obj P ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) (cover.X j) ↘ cover.X j)).obj Q)) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).counit.app P) := by
  let a := AffineSpace (ULift.{u} (Fin 1)) S ↘ S
  let q (j : cover.I₀) := AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j)
  have hq (j : cover.I₀) : Etale (q j) :=
    MorphismProperty.of_isPullback (P := @Etale)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (cover.f j)).flip
      (cover.map_prop j)
  let : ∀ j, Etale (q j) := hq
  apply isIso_of_isIso_upperStar_map_of_jointlySurjective
    (ModuleCat.{u + 1} A) q
  · intro x
    obtain ⟨j, y, hy⟩ := cover.exists_eq (a.base x)
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (cover.f j)) x y hy.symm
    exact ⟨j, z, hz⟩
  · intro j
    let a' := AffineSpace (ULift.{u} (Fin 1)) (cover.X j) ↘ cover.X j
    let : (upperStar (ModuleCat.{u + 1} A) a').Full :=
      etale_a1_pullback_full (cover.X j) A
    let : (upperStar (ModuleCat.{u + 1} A) a').Faithful :=
      line_pullback_faithful A (cover.X j)
    obtain ⟨Q, ⟨e⟩⟩ := hloc j
    have hc := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) a').isIso_counit_app_of_iso e
    have hb := isIso_baseChangeMap_flip_of_isPullback (ModuleCat.{u + 1} A)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (cover.f j)).flip
    have h := upperStar_map_baseChangeMap_app_counit (ModuleCat.{u + 1} A)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (cover.f j)).toCommSq P
    exact (isIso_comp_left_iff
      ((squareUpperStarIso (ModuleCat.{u + 1} A)
        (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1))
          (cover.f j)).toCommSq).hom.app _)
      ((upperStar (ModuleCat.{u + 1} A) (q j)).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) a).counit.app P))).mp
      (h ▸ inferInstance)

private theorem affineLine_full_on_shifted_sheaf
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    {C : DerivedCategoryModule A S} (n : ℤ)
    (hC : ∃ Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty (C⟦n⟧ ≅ (_root_.DerivedCategory.singleFunctor.{u + 1} _ 0).obj Q))
    (v : (L((AffineSpace (ULift.{u} (Fin 1)) S ↘ S)^*[ModuleCat.{u + 1} A])).obj C ⟶
      (L((AffineSpace (ULift.{u} (Fin 1)) S ↘ S)^*[ModuleCat.{u + 1} A])).obj C) :
    ∃ b : C ⟶ C,
      (L((AffineSpace (ULift.{u} (Fin 1)) S ↘ S)^*[ModuleCat.{u + 1} A])).map b = v := by
  obtain ⟨Q, ⟨e⟩⟩ := hC
  let a := upperStar (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  let D : DerivedCategoryModule A S ⥤
      DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S) := a.leftDerivedFunctor
  let σ := _root_.DerivedCategory.singleFunctor.{u + 1}
    (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) 0
  let τ := _root_.DerivedCategory.singleFunctor.{u + 1}
    (Sheaf (AffineSpace (ULift.{u} (Fin 1)) S).smallEtaleTopology
      (ModuleCat.{u + 1} A)) 0
  let : a.Full := etale_a1_pullback_full S A
  let c : σ ⋙ D ≅ a ⋙ τ :=
    singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) _
  have : (σ ⋙ D).Full := Functor.Full.of_iso c.symm
  let v' : D.obj (C⟦n⟧) ⟶ D.obj (C⟦n⟧) :=
    (D.commShiftIso n).hom.app C ≫ v⟦n⟧' ≫ (D.commShiftIso n).inv.app C
  obtain ⟨b₀, hb₀⟩ := (σ ⋙ D).map_surjective
    (D.map e.inv ≫ v' ≫ D.map e.hom)
  let b' : C⟦n⟧ ⟶ C⟦n⟧ := e.hom ≫ σ.map b₀ ≫ e.inv
  have hb' : D.map b' = v' := by
    dsimp [b']
    rw [Functor.map_comp, Functor.map_comp]
    change D.map e.hom ≫ (σ ⋙ D).map b₀ ≫ D.map e.inv = v'
    rw [hb₀]
    simp [← Functor.map_comp_assoc]
  refine ⟨(shiftFunctor _ n).preimage b', (shiftFunctor _ n).map_injective ?_⟩
  have h := D.commShiftIso_hom_naturality ((shiftFunctor _ n).preimage b') n
  rw [Functor.map_preimage, hb'] at h
  rw [← cancel_epi ((D.commShiftIso n).hom.app C), ← h]
  simp only [v', Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem map_eq_of_oneSection (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    {C : DerivedCategoryModule A S} (n : ℤ)
    (hC : ∃ Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty (C⟦n⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj Q))
    {F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S)}
    (f g : F ⟶ (L((AffineSpace (ULift.{u} (Fin 1)) S ↘ S)^*[ModuleCat.{u + 1} A])).obj C)
    [IsIso g]
    (h : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) S)^*[ModuleCat.{u + 1} A])).map f =
      (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) S)^*[ModuleCat.{u + 1} A])).map g) :
    f = g := by
  let D : DerivedCategoryModule A S ⥤
      DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S) :=
    L((AffineSpace (ULift.{u} (Fin 1)) S ↘ S)^*[ModuleCat.{u + 1} A])
  let I : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S) ⥤
      DerivedCategoryModule A S :=
    L((AffineSpace.oneSection (ULift.{u} (Fin 1)) S)^*[ModuleCat.{u + 1} A])
  let c : D ⋙ I ≅ 𝟭 _ := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)
  obtain ⟨b, hb⟩ := affineLine_full_on_shifted_sheaf A S n hC (inv g ≫ f)
  have hn := c.hom.naturality b
  change I.map (D.map b) ≫ c.hom.app C = c.hom.app C ≫ b at hn
  rw [hb, Functor.map_comp, Functor.map_inv, h, IsIso.inv_hom_id, Category.id_comp] at hn
  have hid : b = 𝟙 C := by
    apply (cancel_epi (c.hom.app C)).1
    simpa using hn.symm
  have hratio : inv g ≫ f = 𝟙 (D.obj C) :=
    hb.symm.trans ((congrArg D.map hid).trans (D.map_id C))
  exact (cancel_epi (inv g)).1 (hratio.trans (IsIso.inv_hom_id g).symm)

private theorem pullback_shifted_sheaf (A : Type (u + 1)) [CommRing A]
    {S T : Scheme.{u}} (b : T ⟶ S) {C : DerivedCategoryModule A S} (n : ℤ)
    (hC : ∃ Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty (C⟦n⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj Q)) :
    ∃ Q : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty (((L((b)^*[ModuleCat.{u + 1} A])).obj C)⟦n⟧ ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj Q) := by
  obtain ⟨Q, ⟨e⟩⟩ := hC
  exact ⟨(upperStar (ModuleCat.{u + 1} A) b).obj Q,
    ⟨((L((b)^*[ModuleCat.{u + 1} A])).commShiftIso n).symm.app C ≪≫
      (L((b)^*[ModuleCat.{u + 1} A])).mapIso e ≪≫
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) b).app Q⟩⟩

-- Transport through single complexes, shifts, and the section compositor.
/-- For arbitrary sheaves placed in a common degree, normalized local comparisons give
a normalized global comparison with the prescribed restrictions.
Source: blueprint sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md, Gluing;
Stacks Tags 0A3H, 015F, 06XS, 03EM, and 04TQ.
(blueprint: lem-trf-etale-shifted-line-comparison-existence).

Proof: shift both objects by -m and identify them with the sheaves in the hypotheses.
Exact inverse image preserves these single complexes and its compositors. Full faithfulness
of the single functor therefore turns the local isomorphisms into sheaf isomorphisms.
On the affine line over each pairwise fibre product, the ratio of the two comparisons
restricts to the identity at the unit section. Fullness of affine-line inverse image
lifts this ratio to an endomorphism on the base; its section restriction makes that
endomorphism the identity. Thus both the maps and their inverses agree on overlaps.
The affine-line base changes form an etale cover, so glue the maps and the inverses
by the sheaf morphism gluing theorem. Its uniqueness proves the inverse identities.
Testing on the original base cover proves normalization of the glued map. Undo the
shift and the chosen single-complex identifications to obtain the asserted comparison.
The sheaf gluing theorem includes the empty cover, and this proof uses no nonzero-ring
or reducedness hypothesis. -/
theorem exists_normalized_shifted_line_comparison (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u})
    (m : ℤ) (C : DerivedCategoryModule A S)
    (F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S))
    (hC : ∃ Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty (C⟦-m⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj Q))
    (hF : ∃ P : Sheaf (AffineSpace (ULift.{u} (Fin 1)) S).smallEtaleTopology
        (ModuleCat.{u + 1} A),
      Nonempty (F⟦-m⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj P))
    (θ : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj F ≅ C)
    (cover : Scheme.Cover.{u} Scheme.etalePrecoverage S)
    (localIso : ∀ i : cover.I₀,
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))).leftDerivedFunctor.obj F ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) (cover.X i) ↘ cover.X i)).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) (cover.f i)).leftDerivedFunctor.obj C))
    (hlocal : ∀ i : cover.I₀, sectionRestrictionIso (ModuleCat.{u + 1} A) (cover.f i)
      (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
      (AffineSpace.oneSection_comp_map (cover.f i))
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) (cover.X i))
      θ (localIso i) = Iso.refl _) :
    ∃ κ : F ≅ (L((AffineSpace (ULift.{u} (Fin 1)) S ↘ S)^*[ModuleCat.{u + 1} A])).obj C,
      (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) S)^*[ModuleCat.{u + 1} A])).map κ.hom ≫
        (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
          (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)).hom.app C = θ.hom ∧
      ∀ i : cover.I₀,
        (L((AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))^*[ModuleCat.{u + 1} A])).mapIso κ ≪≫
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
            (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
            (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).app C).symm ≪≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
            (AffineSpace (ULift.{u} (Fin 1)) (cover.X i) ↘ cover.X i) (cover.f i)
            (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i) ≫
              AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
            (AffineSpace.map_over (cover.f i))).app C = localIso i := by
  classical
  let n := -m
  let a := AffineSpace (ULift.{u} (Fin 1)) S ↘ S
  let i := AffineSpace.oneSection (ULift.{u} (Fin 1)) S
  let D : DerivedCategoryModule A S ⥤
      DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S) :=
    L((a)^*[ModuleCat.{u + 1} A])
  let I : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S) ⥤
      DerivedCategoryModule A S := L((i)^*[ModuleCat.{u + 1} A])
  let c : D ⋙ I ≅ 𝟭 _ := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    i a (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)
  obtain ⟨P, ⟨eF⟩⟩ := hF
  obtain ⟨Q, ⟨eC⟩⟩ := hC
  let σ := _root_.DerivedCategory.singleFunctor.{u + 1}
    (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) 0
  let τ := _root_.DerivedCategory.singleFunctor.{u + 1}
    (Sheaf (AffineSpace (ULift.{u} (Fin 1)) S).smallEtaleTopology
      (ModuleCat.{u + 1} A)) 0
  have hcounit := line_counit_isIso A S P cover (fun j ↦ by
    let b := cover.f j
    let q := AffineSpace.map (ULift.{u} (Fin 1)) b
    let a' := AffineSpace (ULift.{u} (Fin 1)) (cover.X j) ↘ cover.X j
    let B := L((b)^*[ModuleCat.{u + 1} A])
    let E := L((q)^*[ModuleCat.{u + 1} A])
    let D' := L((a')^*[ModuleCat.{u + 1} A])
    let R := (upperStar (ModuleCat.{u + 1} A) b).obj Q
    let e : (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} A) q).obj P) ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} A) a').obj R) :=
      ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) q).app P).symm ≪≫
      E.mapIso eF.symm ≪≫ (E.commShiftIso n).app F ≪≫
      (shiftFunctor _ n).mapIso (localIso j) ≪≫
      ((D'.commShiftIso n).app (B.obj C)).symm ≪≫
      D'.mapIso (((B.commShiftIso n).app C).symm ≪≫ B.mapIso eC ≪≫
        (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) b).app Q) ≪≫
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) a').app R
    exact ⟨R, ⟨(_root_.DerivedCategory.singleFunctor _ 0).preimageIso e⟩⟩)
  let R := (lowerStar (ModuleCat.{u + 1} A) a).obj P
  let eP : P ≅ (upperStar (ModuleCat.{u + 1} A) a).obj R :=
    (asIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) a).counit.app P)).symm
  let T := (σ.obj R)⟦-n⟧
  let e : F⟦n⟧ ≅ (D.obj T)⟦n⟧ :=
    eF ≪≫ τ.mapIso eP ≪≫
      ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) a).app R).symm ≪≫
      D.mapIso (((shiftFunctorCompIsoId _ (-n) n (neg_add_cancel n)).app (σ.obj R)).symm) ≪≫
      (D.commShiftIso n).app T
  let κ₀ : F ≅ D.obj T := (shiftFunctor _ n).preimageIso e
  let χ : T ≅ C := (I.mapIso κ₀ ≪≫ c.app T).symm ≪≫ θ
  let κ : F ≅ D.obj C := κ₀ ≪≫ D.mapIso χ
  have hκ : I.map κ.hom ≫ c.hom.app C = θ.hom := by
    dsimp only [κ, Iso.trans_hom, Functor.mapIso_hom]
    rw [Functor.map_comp, Category.assoc]
    have hn := c.hom.naturality χ.hom
    change I.map (D.map χ.hom) ≫ c.hom.app C = c.hom.app T ≫ χ.hom at hn
    rw [hn]
    simp [χ]
  refine ⟨κ, hκ, ?_⟩
  intro j
  let b := cover.f j
  let q := AffineSpace.map (ULift.{u} (Fin 1)) b
  let a' := AffineSpace (ULift.{u} (Fin 1)) (cover.X j) ↘ cover.X j
  let μ := (L((q)^*[ModuleCat.{u + 1} A])).mapIso κ ≪≫
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q a).app C).symm ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a' b (q ≫ a)
      (AffineSpace.map_over b)).app C
  have hμ : sectionRestrictionIso (ModuleCat.{u + 1} A) b q
      (AffineSpace.oneSection_comp_map b)
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) (cover.X j)) θ μ = Iso.refl _ := by
    have hθ : I.mapIso κ ≪≫ c.app C = θ := Iso.ext hκ
    rw [← hθ]
    exact sectionRestrictionIso_restrict (ModuleCat.{u + 1} A) b q
      (AffineSpace.oneSection_comp_map b)
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) (cover.X j))
      (AffineSpace.map_over b) (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S) κ
  apply Iso.ext
  apply map_eq_of_oneSection A (cover.X j) n
    (pullback_shifted_sheaf A b n ⟨Q, ⟨eC⟩⟩)
  exact leftDerivedUpperStar_map_eq_of_sectionRestrictionIso_eq
    (ModuleCat.{u + 1} A) b q (AffineSpace.oneSection_comp_map b)
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) (cover.X j)) θ μ (localIso j)
    (hμ.trans (hlocal j).symm)

end AlgebraicGeometry.Etale
