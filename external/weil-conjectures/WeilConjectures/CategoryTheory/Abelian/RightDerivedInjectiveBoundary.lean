/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison

/-!
# The derived unit on a short exact sequence of bounded below injective complexes

Source: Stacks Project, Derived Categories, Tags 014Q, 0159 and 015B.
(blueprint: lem-sc-p1-right-derived-injective-boundary).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
  [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]

private lemma inverse_shifted_naturality
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ] {X Y : C}
    [IsIso (τ.app X)] [IsIso (τ.app Y)] (f : X ⟶ Y⟦(1 : ℤ)⟧) :
    ShiftedHom.map f G ≫ (inv (τ.app Y))⟦(1 : ℤ)⟧' =
      inv (τ.app X) ≫ ShiftedHom.map f F := by
  have h := ShiftedHom.map_naturality f τ
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
  apply (cancel_epi (τ.app X)).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% h, ← Functor.map_comp]
  simp

private lemma map_Q_comp_ι
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {X Y : CochainComplex.Plus C} (g : X ⟶ Y⟦(1 : ℤ)⟧) :
    ShiftedHom.map g (DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι) =
      ShiftedHom.map g (CochainComplex.Plus.ι C ⋙ DerivedCategory.Q) := by
  have hn := ShiftedHom.map_naturality g (DerivedCategory.Plus.QCompιIso C).hom
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp,
    DerivedCategory.Plus.QCompιIso_hom_app] at hn
  erw [Functor.map_id, Category.comp_id, Category.id_comp] at hn
  exact hn

/-- The cochain derived unit is invertible on a bounded below complex of injectives. -/
lemma isIso_rightDerivedFunctorPlusUnit_of_injective
    (v : A ⥤ B) [v.Additive] (K : CochainComplex.Plus A)
    [∀ n : ℤ, Injective (K.obj.X n)] :
    IsIso (v.rightDerivedFunctorPlusUnit.app K) := by
  let L := HomologicalComplex.liftObjectProperty (isInjective A) K.obj
    (fun n ↦ inferInstance)
  have hL : (CochainComplex.plus (InjectiveObject A)) L := by
    obtain ⟨n, hn⟩ := K.property
    refine ⟨n, ?_⟩
    rwa [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι A)]
  let L' : CochainComplex.Plus (InjectiveObject A) := ⟨L, hL⟩
  have e : (InjectiveObject.ι A).mapCochainComplexPlus.obj L' ≅ K := Iso.refl _
  rw [← NatTrans.isIso_app_iff_of_iso v.rightDerivedFunctorPlusUnit e]
  infer_instance

/-- The inverse derived unit on a bounded below injective complex, followed by
localization's quotient factorization.

Source: Stacks Project, Derived Categories, Tag 015B.
(blueprint: lem-sc-p1-right-derived-injective-boundary). -/
noncomputable def boundedBelowInjectiveComparison
    (v : A ⥤ B) [v.Additive] (K : CochainComplex.Plus A)
    [∀ n : ℤ, Injective (K.obj.X n)] :
    (v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).obj
        (DerivedCategory.Plus.Q.obj K) ⟶
      DerivedCategory.Q.obj ((v.mapHomologicalComplex (.up ℤ)).obj K.obj) := by
  have : IsIso (v.rightDerivedFunctorPlusUnit.app K) := by
    exact isIso_rightDerivedFunctorPlusUnit_of_injective v K
  exact DerivedCategory.Plus.ι.map (inv (v.rightDerivedFunctorPlusUnit.app K))

/-- Lift the canonical SES boundary through the full inclusion of the bounded
below derived category, after the quotient factorization on its endpoints.

Source: Stacks Project, Derived Categories, Tag 014Q.
(blueprint: lem-sc-p1-right-derived-injective-boundary). -/
noncomputable def boundedBelowSESBoundary (H : ShortComplex (CochainComplex.Plus A))
    (hH : (H.map (CochainComplex.plus A).ι).ShortExact) :
    DerivedCategory.Plus.Q.obj H.X₃ ⟶ (DerivedCategory.Plus.Q.obj H.X₁)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Plus.ι.preimage
    (DerivedCategory.triangleOfSESδ hH ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        (DerivedCategory.Plus.Q.obj H.X₁))

set_option backward.isDefEq.respectTransparency false in
/-- The inverse derived units carry the boundary of an injective-complex SES to
that of its termwise image. This is a resolution-level assertion: it does not
involve augmentations, single objects or comparisons with chosen resolutions.

Source: Stacks Project, Derived Categories, Tags 014Q, 0159 and 015B;
fixed-horseshoe comparison Steps 1 and 3.
(blueprint: lem-sc-p1-right-derived-injective-boundary).

Proof: Split each degree row using injectivity of its first object. The proved
DerivedCategory.triangleOfSESδ_eq_degreewiseSplit identifies the source boundary
with localization of CochainComplex.homOfDegreewiseSplit. Apply the additive
functor to the splittings. Its image connecting chain map agrees with the image
of the source connecting chain map followed by the termwise shift comparison:
in each degree both maps are section, image differential, retraction. The same
proved boundary comparison identifies the image SES boundary with this map.
Lift the source connecting map to the bounded below complexes, whose shift is
again bounded below. Naturality of the derived unit at this map, followed by its
shift compatibility, gives the boundary square for the units. The endpoint
units are isomorphisms because the endpoint complexes have injective terms;
invert them. Finally use quotient-factorization naturality and shift
compatibility to obtain exactly the equation with the displayed definitions.
This argument works for zero rows and any common lower bound.
-/
theorem rightDerived_injectiveComplex_boundary
    (v : A ⥤ B) [v.Additive] (H : ShortComplex (CochainComplex.Plus A))
    [∀ n : ℤ, Injective (H.X₁.obj.X n)]
    [∀ n : ℤ, Injective (H.X₂.obj.X n)]
    [∀ n : ℤ, Injective (H.X₃.obj.X n)]
    (hH : (H.map (CochainComplex.plus A).ι).ShortExact)
    (hvH : ((H.map (CochainComplex.plus A).ι).map
      (v.mapHomologicalComplex (.up ℤ))).ShortExact) :
    (v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
        (boundedBelowSESBoundary H hH) ≫
      ((v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Plus.Q.obj H.X₁) ≫
      (boundedBelowInjectiveComparison v H.X₁)⟦(1 : ℤ)⟧' =
    boundedBelowInjectiveComparison v H.X₃ ≫ DerivedCategory.triangleOfSESδ hvH := by
  let S := H.map (CochainComplex.plus A).ι
  let σ (n : ℤ) : (S.map (HomologicalComplex.eval A (.up ℤ) n)).Splitting := by
    have : Injective ((S.map (HomologicalComplex.eval A (.up ℤ) n)).X₁) := by
      change Injective (H.X₁.obj.X n)
      infer_instance
    exact ShortComplex.ShortExact.splittingOfInjective
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hH n)
  let d := CochainComplex.homOfDegreewiseSplit S σ
  let d' : H.X₃ ⟶ H.X₁⟦(1 : ℤ)⟧ := ObjectProperty.homMk
    (d ≫ ((CochainComplex.plus A).ι.commShiftIso (1 : ℤ)).inv.app H.X₁)
  have hd : ShiftedHom.map d' (CochainComplex.plus A).ι = d := by
    change (d ≫ _) ≫ _ = d
    rw [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have hdQ : ShiftedHom.map d' DerivedCategory.Plus.Q =
      boundedBelowSESBoundary H hH := by
    apply DerivedCategory.Plus.ι.map_injective
    apply (cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
      (DerivedCategory.Plus.Q.obj H.X₁))).1
    rw [boundedBelowSESBoundary, Functor.map_preimage, Category.assoc,
      Iso.inv_hom_id_app]
    erw [Category.comp_id]
    change ShiftedHom.map (ShiftedHom.map d' DerivedCategory.Plus.Q)
      DerivedCategory.Plus.ι = _
    rw [← ShiftedHom.comp_map, map_Q_comp_ι, ShiftedHom.comp_map, hd]
    exact (DerivedCategory.triangleOfSESδ_eq_degreewiseSplit S hH σ).symm
  let σv (n : ℤ) : ((S.map (v.mapHomologicalComplex (.up ℤ))).map
      (HomologicalComplex.eval B (.up ℤ) n)).Splitting := (σ n).map v
  have hdv : ShiftedHom.map d (v.mapHomologicalComplex (.up ℤ)) =
      CochainComplex.homOfDegreewiseSplit (S.map (v.mapHomologicalComplex (.up ℤ))) σv := by
    ext n
    simp [ShiftedHom.map, d, CochainComplex.cocycleOfDegreewiseSplit, σv,
      Functor.map_comp]
  have hdv' : ShiftedHom.map (ShiftedHom.map d' v.mapCochainComplexPlus)
      (CochainComplex.Plus.ι B) = ShiftedHom.map d (v.mapHomologicalComplex (.up ℤ)) := by
    have hn := ShiftedHom.map_naturality d' v.mapCochainComplexPlusCompι.hom
    simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp,
      Functor.mapCochainComplexPlusCompι_hom_app, ShiftedHom.comp_map, hd] at hn
    erw [Functor.map_id, Category.comp_id, Category.id_comp] at hn
    exact hn
  let F := (v.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) ⋙ DerivedCategory.Plus.ι
  let G := (DerivedCategory.Plus.Q ⋙ v.rightDerivedFunctorPlus) ⋙ DerivedCategory.Plus.ι
  let τ : F ⟶ G := Functor.whiskerRight v.rightDerivedFunctorPlusUnit
    DerivedCategory.Plus.ι
  have hτ : NatTrans.CommShift τ ℤ := by
    change NatTrans.CommShift
      (Functor.whiskerRight v.rightDerivedFunctorPlusUnit DerivedCategory.Plus.ι) ℤ
    infer_instance
  have hi (K : CochainComplex.Plus A) [∀ n : ℤ, Injective (K.obj.X n)] :
      IsIso (τ.app K) := by
    have := isIso_rightDerivedFunctorPlusUnit_of_injective v K
    change IsIso (DerivedCategory.Plus.ι.map (v.rightDerivedFunctorPlusUnit.app K))
    infer_instance
  have hv : ShiftedHom.map d' F = DerivedCategory.triangleOfSESδ hvH := by
    dsimp only [F]
    rw [ShiftedHom.comp_map, ShiftedHom.comp_map,
      ← ShiftedHom.comp_map _ DerivedCategory.Plus.Q DerivedCategory.Plus.ι,
      map_Q_comp_ι, ShiftedHom.comp_map, hdv', hdv]
    exact (DerivedCategory.triangleOfSESδ_eq_degreewiseSplit _ hvH σv).symm
  have hn := inverse_shifted_naturality τ d'
  change ShiftedHom.map d' G ≫ _ = _ at hn
  dsimp only [G] at hn
  rw [ShiftedHom.comp_map, ShiftedHom.comp_map, hdQ,
    ← ShiftedHom.comp_map _ v.rightDerivedFunctorPlus DerivedCategory.Plus.ι, hv] at hn
  simpa only [ShiftedHom.map, boundedBelowInjectiveComparison, τ,
    Functor.whiskerRight_app, Functor.map_inv, Category.assoc] using hn

end CategoryTheory
