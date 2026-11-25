/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.ConstructibleSheaf.LisseRankOne
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Affine.EtaleAffineLinePullbackFull
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShiftedLineComparisonExistence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-! # Normalized descent of shifted lines on the ordinary etale affine line

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md,
opening paragraph and Gluing (blueprint: lem-trf-etale-shifted-line-normalized-descent).

All pullbacks are the existing ordinary constant-coefficient etale inverse images.
Their total left derived functors agree canonically with the termwise exact functors.
The helper isomorphisms below only compose their prescribed compositors. In particular,
no comparison map or base-change identification is supplied as extra input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

namespace AlgebraicGeometry.Etale.AffineLineNormalizedDescent

/-- The canonical comparison q* a* C ≅ a_T* b* C for the affine-line base-change square.
Source: lemma-section-normal-bundle, Gluing, base change to an etale cover
(blueprint: lem-trf-etale-shifted-line-normalized-descent). -/
def lineBaseChange (A : Type (u + 1)) [CommRing A] {T S : Scheme.{u}}
    (b : T ⟶ S) (C : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj C) ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj C) :=
  ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace.map (ULift.{u} (Fin 1)) b)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).app C).symm ≪≫
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) b
    (AffineSpace.map (ULift.{u} (Fin 1)) b ≫ AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace.map_over b)).app C

/-- Normalization at the unit section, using the specified section compositor.
Source: lemma-section-normal-bundle, Gluing, identity at t=1
(blueprint: lem-trf-etale-shifted-line-normalized-descent). -/
def Normalized (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    {F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S)}
    {C : DerivedCategoryModule A S}
    (θ : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj F ≅ C)
    (κ : F ≅ (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj C) : Prop :=
  (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map κ.hom ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)).hom.app C = θ.hom

/-- Local normalization: the local comparison evaluated at one is b* theta.
The existing sectionRestrictionIso includes both the section-square compositor and
cancellation of a_T* along its section, so equality to the identity expresses precisely
this normalization, without choosing identifications.
Source: lemma-section-normal-bundle, Gluing (blueprint:
lem-trf-etale-shifted-line-normalized-descent). -/
def LocallyNormalized (A : Type (u + 1)) [CommRing A] {T S : Scheme.{u}} (b : T ⟶ S)
    {F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S)}
    {C : DerivedCategoryModule A S}
    (θ : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj F ≅ C)
    (localIso : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj F ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj C)) : Prop :=
  sectionRestrictionIso (ModuleCat.{u + 1} A) b
    (AffineSpace.map (ULift.{u} (Fin 1)) b)
    (AffineSpace.oneSection_comp_map b)
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) T) θ localIso = Iso.refl _

/-- Restrict a local comparison to a further object, identifying both endpoints by
inverse-image compositors. This is used on the actual fibre-product overlaps.
Source: lemma-section-normal-bundle, Gluing (blueprint:
lem-trf-etale-shifted-line-normalized-descent). -/
def comparisonRestriction (A : Type (u + 1)) [CommRing A]
    {W U X : Scheme.{u}} (f : U ⟶ X) (g : W ⟶ U) (h : W ⟶ X) (hh : h = g ≫ f)
    {F G : DerivedCategoryModule A X}
    (e : (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj F ≅
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj G) :
    (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj F ≅
      (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj G :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g f h hh).app F ≪≫
    (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.mapIso e ≪≫
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g f h hh).app G).symm

open scoped AlgebraicGeometry.Etale

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

private theorem comparisonRestriction_mapIso (A : Type (u + 1)) [CommRing A]
    {W U X : Scheme.{u}} (f : U ⟶ X) (g : W ⟶ U) (h : W ⟶ X) (hh : h = g ≫ f)
    {F G : DerivedCategoryModule A X} (κ : F ≅ G) :
    comparisonRestriction A f g h hh ((L((f)^*[ModuleCat.{u + 1} A])).mapIso κ) =
      (L((h)^*[ModuleCat.{u + 1} A])).mapIso κ := by
  apply Iso.ext
  exact NatIso.naturality_2 (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g f h hh) κ.hom

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

private theorem local_comparison_unique (A : Type (u + 1)) [CommRing A]
    {S T : Scheme.{u}} (b : T ⟶ S)
    {F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S)}
    {C : DerivedCategoryModule A S}
    (n : ℤ) (hC : ∃ Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty (C⟦n⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj Q))
    (θ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) S)^*[ModuleCat.{u + 1} A])).obj F ≅ C)
    (α β : (L((AffineSpace.map (ULift.{u} (Fin 1)) b)^*[ModuleCat.{u + 1} A])).obj F ≅
      (L((AffineSpace (ULift.{u} (Fin 1)) T ↘ T)^*[ModuleCat.{u + 1} A])).obj
        ((L((b)^*[ModuleCat.{u + 1} A])).obj C))
    (hα : LocallyNormalized A b θ α) (hβ : LocallyNormalized A b θ β) : α = β := by
  apply Iso.ext
  apply map_eq_of_oneSection A T n (pullback_shifted_sheaf A b n hC)
  exact leftDerivedUpperStar_map_eq_of_sectionRestrictionIso_eq
    (ModuleCat.{u + 1} A) b (AffineSpace.map (ULift.{u} (Fin 1)) b)
    (AffineSpace.oneSection_comp_map b)
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) T) θ α β (hα.trans hβ.symm)

/-- Normalized local comparisons of shifted ordinary-etale lines agree, as do their
inverses, and descend to a globally normalized isomorphism. Global uniqueness quantifies
over all normalized isomorphisms. The last clause gives independence on every etale
base change, hence independence of the entire cover and all normalized choices.
Source: sk-thm-dnc.proof.md, opening paragraph and Gluing
(blueprint: lem-trf-etale-shifted-line-normalized-descent).
Proof: Step 1 is sheaf_rigidity, by affine-line fullness (Stacks 0A3H). Step 2 fixes
F[-m]=P[0] and C[-m]=Q[0]. Exact inverse image commutes with shifts and single complexes
(015F); the fully faithful single functor (06XS) identifies maps, inverses and their
compositions with sheaf maps, compatibly with every compositor. Step 3 uses affine-space
base change to identify X_i and all overlaps with affine lines over the corresponding
bases. Etale covering-base-change makes the X_i cover X, including empty covers.
Step 4 takes the ratio of two local comparisons on an overlap; normalization makes
its value at one the identity, so Step 1 makes the ratio the identity. Inverses agree
as well. Step 5 applies existsUnique_etaleSheafHom_of_family to glue the maps and
separately their inverses; uniqueness identifies both composites with identities.
Return to derived objects by Step 2. Step 6 tests the normalization on the base cover.
The ratio of any two normalized global comparisons is the identity by Step 1, without
assuming prescribed restrictions. Apply that argument over every etale base to identify
any other normalized local comparison with the restriction of the global one. This
includes empty and nonreduced bases and the zero ring. -/
theorem normalized_descent (A : Type (u + 1)) [CommRing A] [Finite A] (S : Scheme.{u})
    (m : ℤ) (C : DerivedCategoryModule A S)
    (F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S))
    (hC : ∃ Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A),
      Scheme.IsLisseRankOneSheaf Q ∧
        Nonempty (C⟦-m⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj Q))
    (hF : ∃ P : Sheaf (AffineSpace (ULift.{u} (Fin 1)) S).smallEtaleTopology
        (ModuleCat.{u + 1} A), Scheme.IsLisseRankOneSheaf P ∧
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
    (hlocal : ∀ i : cover.I₀, LocallyNormalized A (cover.f i) θ (localIso i)) :
    (∀ i j : cover.I₀,
      comparisonRestriction A (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
        (pullback.fst (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
          (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))) _ rfl
        (localIso i ≪≫ (lineBaseChange A (cover.f i) C).symm) =
      comparisonRestriction A (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))
        (pullback.snd (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
          (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))) _ pullback.condition
        (localIso j ≪≫ (lineBaseChange A (cover.f j) C).symm)) ∧
    (∀ i j : cover.I₀,
      (comparisonRestriction A (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
        (pullback.fst (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
          (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))) _ rfl
        (localIso i ≪≫ (lineBaseChange A (cover.f i) C).symm)).inv =
      (comparisonRestriction A (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))
        (pullback.snd (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
          (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))) _ pullback.condition
        (localIso j ≪≫ (lineBaseChange A (cover.f j) C).symm)).inv) ∧
    ∃ κ : F ≅ (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj C,
      Normalized A S θ κ ∧
      (∀ i : cover.I₀,
        (upperStar (ModuleCat.{u + 1} A)
          (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))).leftDerivedFunctor.mapIso κ ≪≫
          lineBaseChange A (cover.f i) C = localIso i) ∧
      (∀ κ' : F ≅ (upperStar (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj C,
        Normalized A S θ κ' → κ' = κ) ∧
      (∀ (T : Scheme.{u}) (b : T ⟶ S), Etale b →
        ∀ μ : (upperStar (ModuleCat.{u + 1} A)
            (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj F ≅
          (upperStar (ModuleCat.{u + 1} A)
            (AffineSpace (ULift.{u} (Fin 1)) T ↘ T)).leftDerivedFunctor.obj
              ((upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj C),
        LocallyNormalized A b θ μ →
          μ = (upperStar (ModuleCat.{u + 1} A)
            (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.mapIso κ ≪≫
              lineBaseChange A b C) := by
  have hC' := hC.imp fun _ h ↦ h.2
  obtain ⟨κ, hκ, hκres⟩ := exists_normalized_shifted_line_comparison
    A S m C F hC' (hF.imp fun _ h ↦ h.2) θ cover localIso hlocal
  change Normalized A S θ κ at hκ
  change ∀ i, (L((AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))^*[
    ModuleCat.{u + 1} A])).mapIso κ ≪≫ lineBaseChange A (cover.f i) C = localIso i at hκres
  have hres (i : cover.I₀) : localIso i ≪≫ (lineBaseChange A (cover.f i) C).symm =
      (L((AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))^*[ModuleCat.{u + 1} A])).mapIso κ := by
    rw [← hκres i]
    simp
  have hcompat (i j : cover.I₀) :
      comparisonRestriction A (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
        (pullback.fst (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
          (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))) _ rfl
        (localIso i ≪≫ (lineBaseChange A (cover.f i) C).symm) =
      comparisonRestriction A (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))
        (pullback.snd (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
          (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f j))) _ pullback.condition
        (localIso j ≪≫ (lineBaseChange A (cover.f j) C).symm) := by
    rw [hres i, hres j, comparisonRestriction_mapIso, comparisonRestriction_mapIso]
  refine ⟨hcompat, fun i j ↦ congrArg Iso.inv (hcompat i j), κ, hκ, hκres, ?_, ?_⟩
  · intro κ' hκ'
    apply Iso.ext
    apply map_eq_of_oneSection A S (-m) hC'
    exact (cancel_mono
      ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)).hom.app C)).1
      (hκ'.trans hκ.symm)
  · intro T b _ μ hμ
    apply local_comparison_unique A b (-m) hC' θ μ _ hμ
    have hθ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) S)^*[
        ModuleCat.{u + 1} A])).mapIso κ ≪≫
        (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
          (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)).app C = θ :=
      Iso.ext hκ
    change sectionRestrictionIso (ModuleCat.{u + 1} A) b _ _ _ θ _ = Iso.refl _
    rw [← hθ]
    exact sectionRestrictionIso_restrict (ModuleCat.{u + 1} A) b
      (AffineSpace.map (ULift.{u} (Fin 1)) b) (AffineSpace.oneSection_comp_map b)
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) T)
      (AffineSpace.map_over b) (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S) κ

end AlgebraicGeometry.Etale.AffineLineNormalizedDescent
