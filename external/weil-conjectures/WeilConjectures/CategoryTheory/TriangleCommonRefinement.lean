/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import WeilConjectures.CategoryTheory.Triangulated.DenominatorTriangleCompletion
import Mathlib.Data.Fintype.Option

/-! # Common refinements of denominator triangles

Source: Stacks Project, Derived Categories, Tag 05R9, with arrows reversed
(blueprint: lem-pur-triangle-common-refinement-ms3-05r9).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

private def Denom {C : Type u} [Category.{v} C] [HasShift C ℤ]
    (S : MorphismProperty C) {D E : Triangle C} (s : D ⟶ E) : Prop :=
  S s.hom₁ ∧ S s.hom₂ ∧ S s.hom₃

private lemma denom_comp {C : Type u} [Category.{v} C] [HasShift C ℤ]
    (S : MorphismProperty C) (hcomp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
      S f → S g → S (f ≫ g))
    {D E F : Triangle C} {s : D ⟶ E} {t : E ⟶ F}
    (hs : Denom S s) (ht : Denom S t) : Denom S (s ≫ t) :=
  ⟨hcomp _ _ hs.1 ht.1, hcomp _ _ hs.2.1 ht.2.1,
    hcomp _ _ hs.2.2 ht.2.2⟩

private lemma mem_of_comp {C : Type u} [Category.{v} C] (S : MorphismProperty C)
    (hS : S.IsSaturatedMultiplicativeSystem) {X Y Z : C}
    (f : X ⟶ Y) (s : Y ⟶ Z) (hs : S s) (hfs : S (f ≫ s)) : S f := by
  have : S.HasRightCalculusOfFractions := hS.1.2
  let : S.IsStableUnderComposition := hS.1.1.1.toIsStableUnderComposition
  obtain ⟨ψ, hψ⟩ :=
    (MorphismProperty.LeftFraction.mk s (f ≫ s) hfs).exists_rightFraction
  obtain ⟨W, z, hz, he⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
    ψ.s (ψ.f ≫ f) s hs (by simpa only [Category.assoc] using hψ)
  apply hS.2 _ _ _ _ (z ≫ ψ.f) f s hfs
  simpa only [Category.assoc, ← he] using S.comp_mem z ψ.s hz ψ.hs

private lemma equalize
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : MorphismProperty C) (hS : S.IsSaturatedMultiplicativeSystem)
    [S.IsCompatibleWithTriangulation] {D E F : Triangle C}
    (hD : D ∈ distTriang C) (a b : D ⟶ E) (t : E ⟶ F)
    (ht : Denom S t)
    (hab : a ≫ t = b ≫ t) :
    ∃ (U : Triangle C) (q : U ⟶ D), U ∈ distTriang C ∧ Denom S q ∧
      q ≫ a = q ≫ b := by
  have : S.HasRightCalculusOfFractions := hS.1.2
  obtain ⟨X, x, hx, he₁⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
    a.hom₁ b.hom₁ t.hom₁ ht.1 (congrArg TriangleMorphism.hom₁ hab)
  obtain ⟨Y, Z, f, g, h, hU, q₁, hq₁, hq₁₂, hq₁₃⟩ :=
    (denominator_triangle_completion S hS D hD).1 X x hx
  have hq₁S : Denom S q₁ := ⟨hq₁ ▸ hx, hq₁₂, hq₁₃⟩
  have he₁' : (q₁ ≫ a).hom₁ = (q₁ ≫ b).hom₁ := by
    simpa only [comp_hom₁, hq₁] using he₁
  have hab₁ : (q₁ ≫ a) ≫ t = (q₁ ≫ b) ≫ t := by rw [Category.assoc, Category.assoc, hab]
  obtain ⟨Y₂, y, hy, he₂⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
    (q₁ ≫ a).hom₂ (q₁ ≫ b).hom₂ t.hom₂ ht.2.1
    (congrArg TriangleMorphism.hom₂ hab₁)
  obtain ⟨X₂, Z₂, f₂, g₂, h₂, hV, q₂, hq₂, hq₂₁, hq₂₃⟩ :=
    (denominator_triangle_completion S hS _ hU).2.1 Y₂ y hy
  have hq₂S : Denom S q₂ := ⟨hq₂₁, hq₂ ▸ hy, hq₂₃⟩
  have he₂' : (q₂ ≫ q₁ ≫ a).hom₂ = (q₂ ≫ q₁ ≫ b).hom₂ := by
    simpa only [comp_hom₂, hq₂] using he₂
  have hab₂ : (q₂ ≫ q₁ ≫ a) ≫ t = (q₂ ≫ q₁ ≫ b) ≫ t := by
    simp only [Category.assoc, hab]
  obtain ⟨Z₃, z, hz, he₃⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
    (q₂ ≫ q₁ ≫ a).hom₃ (q₂ ≫ q₁ ≫ b).hom₃ t.hom₃ ht.2.2
    (congrArg TriangleMorphism.hom₃ hab₂)
  obtain ⟨X₃, Y₃, f₃, g₃, h₃, hW, q₃, hq₃, hq₃₁, hq₃₂⟩ :=
    (denominator_triangle_completion S hS _ hV).2.2 Z₃ z hz
  have hq₃S : Denom S q₃ := ⟨hq₃₁, hq₃₂, hq₃ ▸ hz⟩
  refine ⟨_, q₃ ≫ q₂ ≫ q₁, hW,
    denom_comp S (fun _ _ => S.comp_mem _ _) hq₃S
      (denom_comp S (fun _ _ => S.comp_mem _ _) hq₂S hq₁S), ?_⟩
  apply Triangle.hom_ext
  · simpa only [comp_hom₁, Category.assoc] using
      congrArg (fun k => q₃.hom₁ ≫ q₂.hom₁ ≫ k) he₁'
  · simpa only [comp_hom₂, Category.assoc] using
      congrArg (fun k => q₃.hom₂ ≫ k) he₂'
  · simpa only [comp_hom₃, Category.assoc, hq₃] using he₃

private lemma rectify
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : MorphismProperty C) (hS : S.IsSaturatedMultiplicativeSystem)
    [S.IsCompatibleWithTriangulation] {A E T : Triangle C}
    (hA : A ∈ distTriang C) (v : A ⟶ T) (t : E ⟶ T) (ht : Denom S t)
    (c₁ : A.obj₁ ⟶ E.obj₁) (c₂ : A.obj₂ ⟶ E.obj₂) (c₃ : A.obj₃ ⟶ E.obj₃)
    (sc₁ : S c₁) (sc₂ : S c₂) (sc₃ : S c₃)
    (ec₁ : c₁ ≫ t.hom₁ = v.hom₁) (ec₂ : c₂ ≫ t.hom₂ = v.hom₂)
    (ec₃ : c₃ ≫ t.hom₃ = v.hom₃) :
    ∃ (U : Triangle C) (q : U ⟶ A) (b : U ⟶ E), U ∈ distTriang C ∧
      Denom S q ∧ Denom S b ∧ q ≫ v = b ≫ t := by
  have : S.HasRightCalculusOfFractions := hS.1.2
  have eh₁ : (A.mor₁ ≫ c₂) ≫ t.hom₂ = (c₁ ≫ E.mor₁) ≫ t.hom₂ := by
    rw [Category.assoc, ec₂, Category.assoc, t.comm₁, ← Category.assoc, ec₁]
    exact v.comm₁
  obtain ⟨X₁, x, sx, ex⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
    (A.mor₁ ≫ c₂) (c₁ ≫ E.mor₁) t.hom₂ ht.2.1 eh₁
  obtain ⟨Y₁, Z₁, f₁, g₁, h₁, hB, q₁, eq₁, sq₁₂, sq₁₃⟩ :=
    (denominator_triangle_completion S hS A hA).1 X₁ x sx
  have sq₁ : Denom S q₁ := ⟨eq₁ ▸ sx, sq₁₂, sq₁₃⟩
  have comm₁ : f₁ ≫ q₁.hom₂ ≫ c₂ = (q₁.hom₁ ≫ c₁) ≫ E.mor₁ := by
    rw [← Category.assoc, show f₁ ≫ q₁.hom₂ = q₁.hom₁ ≫ A.mor₁ from q₁.comm₁,
      Category.assoc, eq₁]
    simpa only [Category.assoc] using ex
  have eh₂ : (g₁ ≫ q₁.hom₃ ≫ c₃) ≫ t.hom₃ =
      ((q₁.hom₂ ≫ c₂) ≫ E.mor₂) ≫ t.hom₃ := by
    calc
      _ = g₁ ≫ q₁.hom₃ ≫ v.hom₃ := by simp only [Category.assoc, ec₃]
      _ = q₁.hom₂ ≫ A.mor₂ ≫ v.hom₃ := by
        rw [← Category.assoc,
          show g₁ ≫ q₁.hom₃ = q₁.hom₂ ≫ A.mor₂ from q₁.comm₂, Category.assoc]
      _ = q₁.hom₂ ≫ v.hom₂ ≫ T.mor₂ := by rw [v.comm₂]
      _ = _ := by rw [← ec₂]; simp only [Category.assoc, t.comm₂]
  obtain ⟨Y₂, y, sy, ey⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
    (g₁ ≫ q₁.hom₃ ≫ c₃) ((q₁.hom₂ ≫ c₂) ≫ E.mor₂) t.hom₃ ht.2.2 eh₂
  obtain ⟨X₂, Z₂, f₂, g₂, h₂, hB₂, q₂, eq₂, sq₂₁, sq₂₃⟩ :=
    (denominator_triangle_completion S hS _ hB).2.1 Y₂ y sy
  have sq₂ : Denom S q₂ := ⟨sq₂₁, eq₂ ▸ sy, sq₂₃⟩
  have comm₂ : g₂ ≫ q₂.hom₃ ≫ q₁.hom₃ ≫ c₃ =
      (q₂.hom₂ ≫ q₁.hom₂ ≫ c₂) ≫ E.mor₂ := by
    rw [← Category.assoc,
      show g₂ ≫ q₂.hom₃ = q₂.hom₂ ≫ g₁ from q₂.comm₂, Category.assoc, eq₂]
    simpa only [Category.assoc] using ey
  let d₁ := q₂.hom₁ ≫ q₁.hom₁ ≫ c₁
  let d₂ := q₂.hom₂ ≫ q₁.hom₂ ≫ c₂
  let d₃ := q₂.hom₃ ≫ q₁.hom₃ ≫ c₃
  have eh₃ : (h₂ ≫ d₁⟦(1 : ℤ)⟧') ≫ t.hom₁⟦(1 : ℤ)⟧' =
      (d₃ ≫ E.mor₃) ≫ t.hom₁⟦(1 : ℤ)⟧' := by
    have ev₁ : d₁ ≫ t.hom₁ = (q₂ ≫ q₁ ≫ v).hom₁ := by
      change (q₂.hom₁ ≫ q₁.hom₁ ≫ c₁) ≫ t.hom₁ =
        q₂.hom₁ ≫ q₁.hom₁ ≫ v.hom₁
      simp only [Category.assoc, ec₁]
    have ev₃ : d₃ ≫ t.hom₃ = (q₂ ≫ q₁ ≫ v).hom₃ := by
      change (q₂.hom₃ ≫ q₁.hom₃ ≫ c₃) ≫ t.hom₃ =
        q₂.hom₃ ≫ q₁.hom₃ ≫ v.hom₃
      simp only [Category.assoc, ec₃]
    calc
      _ = h₂ ≫ ((q₂ ≫ q₁ ≫ v).hom₁)⟦(1 : ℤ)⟧' := by
        rw [Category.assoc, ← Functor.map_comp, ev₁]
      _ = (q₂ ≫ q₁ ≫ v).hom₃ ≫ T.mor₃ := (q₂ ≫ q₁ ≫ v).comm₃
      _ = _ := by
        rw [Category.assoc, t.comm₃]
        simpa only [Category.assoc] using
          (congrArg (fun k => k ≫ T.mor₃) ev₃).symm
  obtain ⟨Z₃, z, sz, ez⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
    (h₂ ≫ d₁⟦(1 : ℤ)⟧') (d₃ ≫ E.mor₃) (t.hom₁⟦(1 : ℤ)⟧')
    (S.shift ht.1 (1 : ℤ)) eh₃
  obtain ⟨X₃, Y₃, f₃, g₃, h₃, hU, q₃, eq₃, sq₃₁, sq₃₂⟩ :=
    (denominator_triangle_completion S hS _ hB₂).2.2 Z₃ z sz
  have sq₃ : Denom S q₃ := ⟨sq₃₁, sq₃₂, eq₃ ▸ sz⟩
  have cb₁ : f₃ ≫ q₃.hom₂ ≫ d₂ = (q₃.hom₁ ≫ d₁) ≫ E.mor₁ := by
    change f₃ ≫ q₃.hom₂ ≫ q₂.hom₂ ≫ q₁.hom₂ ≫ c₂ =
      (q₃.hom₁ ≫ q₂.hom₁ ≫ q₁.hom₁ ≫ c₁) ≫ E.mor₁
    rw [← Category.assoc,
      show f₃ ≫ q₃.hom₂ = q₃.hom₁ ≫ f₂ from q₃.comm₁, Category.assoc,
      ← Category.assoc f₂ q₂.hom₂,
      show f₂ ≫ q₂.hom₂ = q₂.hom₁ ≫ f₁ from q₂.comm₁]
    simpa only [Category.assoc] using
      congrArg (fun k => q₃.hom₁ ≫ q₂.hom₁ ≫ k) comm₁
  have cb₂ : g₃ ≫ q₃.hom₃ ≫ d₃ = (q₃.hom₂ ≫ d₂) ≫ E.mor₂ := by
    rw [← Category.assoc,
      show g₃ ≫ q₃.hom₃ = q₃.hom₂ ≫ g₂ from q₃.comm₂, Category.assoc]
    simpa only [d₂, d₃, Category.assoc] using
      congrArg (fun k => q₃.hom₂ ≫ k) comm₂
  have cb₃ : h₃ ≫ (q₃.hom₁ ≫ d₁)⟦(1 : ℤ)⟧' =
      (q₃.hom₃ ≫ d₃) ≫ E.mor₃ := by
    rw [Functor.map_comp, ← Category.assoc,
      show h₃ ≫ q₃.hom₁⟦(1 : ℤ)⟧' = q₃.hom₃ ≫ h₂ from q₃.comm₃,
      Category.assoc, eq₃]
    simpa only [Category.assoc] using ez
  let b : Triangle.mk f₃ g₃ h₃ ⟶ E :=
    Triangle.homMk _ _ (q₃.hom₁ ≫ d₁) (q₃.hom₂ ≫ d₂) (q₃.hom₃ ≫ d₃)
      cb₁ cb₂ cb₃
  have sb : Denom S b :=
    ⟨S.comp_mem _ _ sq₃.1 (S.comp_mem _ _ sq₂.1 (S.comp_mem _ _ sq₁.1 sc₁)),
      S.comp_mem _ _ sq₃.2.1
        (S.comp_mem _ _ sq₂.2.1 (S.comp_mem _ _ sq₁.2.1 sc₂)),
      S.comp_mem _ _ sq₃.2.2
        (S.comp_mem _ _ sq₂.2.2 (S.comp_mem _ _ sq₁.2.2 sc₃))⟩
  refine ⟨_, q₃ ≫ q₂ ≫ q₁, b, hU,
    denom_comp S (fun _ _ => S.comp_mem _ _) sq₃
      (denom_comp S (fun _ _ => S.comp_mem _ _) sq₂ sq₁), sb, ?_⟩
  apply Triangle.hom_ext
  · change (q₃.hom₁ ≫ q₂.hom₁ ≫ q₁.hom₁) ≫ v.hom₁ =
      (q₃.hom₁ ≫ q₂.hom₁ ≫ q₁.hom₁ ≫ c₁) ≫ t.hom₁
    simp only [Category.assoc, ec₁]
  · change (q₃.hom₂ ≫ q₂.hom₂ ≫ q₁.hom₂) ≫ v.hom₂ =
      (q₃.hom₂ ≫ q₂.hom₂ ≫ q₁.hom₂ ≫ c₂) ≫ t.hom₂
    simp only [Category.assoc, ec₂]
  · change (q₃.hom₃ ≫ q₂.hom₃ ≫ q₁.hom₃) ≫ v.hom₃ =
      (q₃.hom₃ ≫ q₂.hom₃ ≫ q₁.hom₃ ≫ c₃) ≫ t.hom₃
    simp only [Category.assoc, ec₃]

private lemma binary_refinement
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : MorphismProperty C) (hS : S.IsSaturatedMultiplicativeSystem)
    [S.IsCompatibleWithTriangulation] {T D E : Triangle C}
    (hD : D ∈ distTriang C) (_hE : E ∈ distTriang C)
    (s : D ⟶ T) (t : E ⟶ T) (hs : Denom S s) (ht : Denom S t) :
    ∃ (U : Triangle C) (a : U ⟶ D) (b : U ⟶ E),
      U ∈ distTriang C ∧ Denom S a ∧ Denom S b ∧ a ≫ s = b ≫ t := by
  have : S.HasRightCalculusOfFractions := hS.1.2
  obtain ⟨ψ₁, e₁⟩ :=
    (MorphismProperty.LeftFraction.mk s.hom₁ t.hom₁ ht.1).exists_rightFraction
  obtain ⟨Y₁, Z₁, f₁, g₁, h₁, hA, q₁, eq₁, sq₁₂, sq₁₃⟩ :=
    (denominator_triangle_completion S hS D hD).1 _ ψ₁.s ψ₁.hs
  have sq₁ : Denom S q₁ := ⟨eq₁ ▸ ψ₁.hs, sq₁₂, sq₁₃⟩
  obtain ⟨ψ₂, e₂⟩ :=
    (MorphismProperty.LeftFraction.mk (q₁ ≫ s).hom₂ t.hom₂ ht.2.1).exists_rightFraction
  obtain ⟨X₂, Z₂, f₂, g₂, h₂, hB, q₂, eq₂, sq₂₁, sq₂₃⟩ :=
    (denominator_triangle_completion S hS _ hA).2.1 _ ψ₂.s ψ₂.hs
  have sq₂ : Denom S q₂ := ⟨sq₂₁, eq₂ ▸ ψ₂.hs, sq₂₃⟩
  obtain ⟨ψ₃, e₃⟩ :=
    (MorphismProperty.LeftFraction.mk (q₂ ≫ q₁ ≫ s).hom₃ t.hom₃ ht.2.2).exists_rightFraction
  obtain ⟨X₃, Y₃, f₃, g₃, h₃, hA₃, q₃, eq₃, sq₃₁, sq₃₂⟩ :=
    (denominator_triangle_completion S hS _ hB).2.2 _ ψ₃.s ψ₃.hs
  have sq₃ : Denom S q₃ := ⟨sq₃₁, sq₃₂, eq₃ ▸ ψ₃.hs⟩
  let u := q₃ ≫ q₂ ≫ q₁
  have su : Denom S u := denom_comp S (fun _ _ => S.comp_mem _ _) sq₃
    (denom_comp S (fun _ _ => S.comp_mem _ _) sq₂ sq₁)
  let c₁ := q₃.hom₁ ≫ q₂.hom₁ ≫ ψ₁.f
  let c₂ := q₃.hom₂ ≫ ψ₂.f
  let c₃ := ψ₃.f
  have ec₁ : c₁ ≫ t.hom₁ = (u ≫ s).hom₁ := by
    change (q₃.hom₁ ≫ q₂.hom₁ ≫ ψ₁.f) ≫ t.hom₁ =
      (q₃.hom₁ ≫ q₂.hom₁ ≫ q₁.hom₁) ≫ s.hom₁
    simp only [Category.assoc, eq₁]
    rw [← e₁]
  have ec₂ : c₂ ≫ t.hom₂ = (u ≫ s).hom₂ := by
    change (q₃.hom₂ ≫ ψ₂.f) ≫ t.hom₂ =
      (q₃.hom₂ ≫ q₂.hom₂ ≫ q₁.hom₂) ≫ s.hom₂
    simp only [comp_hom₂] at e₂
    simp only [Category.assoc, eq₂]
    rw [← e₂]
  have ec₃ : c₃ ≫ t.hom₃ = (u ≫ s).hom₃ := by
    change ψ₃.f ≫ t.hom₃ = (q₃.hom₃ ≫ q₂.hom₃ ≫ q₁.hom₃) ≫ s.hom₃
    simpa only [comp_hom₃, Category.assoc, eq₃] using e₃.symm
  have sc₁ : S c₁ := mem_of_comp S hS c₁ t.hom₁ ht.1
    (ec₁.symm ▸ S.comp_mem _ _ su.1 hs.1)
  have sc₂ : S c₂ := mem_of_comp S hS c₂ t.hom₂ ht.2.1
    (ec₂.symm ▸ S.comp_mem _ _ su.2.1 hs.2.1)
  have sc₃ : S c₃ := mem_of_comp S hS c₃ t.hom₃ ht.2.2
    (ec₃.symm ▸ S.comp_mem _ _ su.2.2 hs.2.2)
  obtain ⟨U, q, b, hU, sq, sb, eq⟩ :=
    rectify S hS hA₃ (u ≫ s) t ht c₁ c₂ c₃ sc₁ sc₂ sc₃ ec₁ ec₂ ec₃
  exact ⟨U, q ≫ u, b, hU, denom_comp S (fun _ _ => S.comp_mem _ _) sq su,
    sb, by simpa only [Category.assoc] using eq⟩

private lemma finite_triangle_refinement
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : MorphismProperty C) (hS : S.IsSaturatedMultiplicativeSystem)
    [S.IsCompatibleWithTriangulation] (T : Triangle C) (hT : T ∈ distTriang C) :
    ∀ (I : Type w) [Finite I] (D : I → Triangle C) (s : ∀ i : I, D i ⟶ T),
      (∀ i : I, D i ∈ distTriang C) →
      (∀ i : I, Denom S (s i)) →
      ∃ (U : Triangle C) (t : U ⟶ T), U ∈ distTriang C ∧ Denom S t ∧
        ∀ i : I, ∃ a : U ⟶ D i, Denom S a ∧ a ≫ s i = t := by
  intro I _
  have : S.HasRightCalculusOfFractions := hS.1.2
  let P := fun I : Type w =>
    ∀ (D : I → Triangle C) (s : ∀ i : I, D i ⟶ T),
      (∀ i : I, D i ∈ distTriang C) → (∀ i : I, Denom S (s i)) →
      ∃ (U : Triangle C) (t : U ⟶ T), U ∈ distTriang C ∧ Denom S t ∧
        ∀ i : I, ∃ a : U ⟶ D i, Denom S a ∧ a ≫ s i = t
  change P I
  apply Finite.induction_empty_option (P := P) ?_ ?_ ?_ I
  · intro α β e ih D s hD hs
    obtain ⟨U, t, hU, ht, hu⟩ := ih (fun i => D (e i)) (fun i => s (e i))
      (fun i => hD (e i)) (fun i => hs (e i))
    refine ⟨U, t, hU, ht, ?_⟩
    intro i
    have hi := hu (e.symm i)
    change ∃ (a : U ⟶ D (e (e.symm i))),
      Denom S a ∧ a ≫ s (e (e.symm i)) = t at hi
    exact e.apply_symm_apply i ▸ hi
  · intro D s hD hs
    refine ⟨T, 𝟙 T, hT, ⟨S.id_mem _, S.id_mem _, S.id_mem _⟩, ?_⟩
    intro i
    exact PEmpty.elim i
  · intro α _ ih D s hD hs
    obtain ⟨U, t, hU, ht, hu⟩ := ih (fun i => D (some i)) (fun i => s (some i))
      (fun i => hD (some i)) (fun i => hs (some i))
    obtain ⟨V, a, b, hV, ha, hb, eq⟩ :=
      binary_refinement S hS hU (hD none) t (s none) ht (hs none)
    refine ⟨V, a ≫ t, hV, denom_comp S (fun _ _ => S.comp_mem _ _) ha ht, ?_⟩
    intro i
    cases i with
    | none => exact ⟨b, hb, eq.symm⟩
    | some i =>
      obtain ⟨c, hc, ec⟩ := hu i
      exact ⟨a ≫ c, denom_comp S (fun _ _ => S.comp_mem _ _) ha hc,
        by rw [Category.assoc, ec]⟩

/-- Finite families of distinguished denominator triangles over `T` have a common predecessor,
and parallel denominator triangle morphisms are equalized by another denominator triangle.
Source: Stacks Project, Derived Categories, Tag 05R9, dual construction
(blueprint: lem-pur-triangle-common-refinement-ms3-05r9).

Proof: (1) The right fraction calculus makes `S/X` cofiltered. Saturation ensures every
commuting arrow between denominators lies in `S`: use MS2 to complete a square, MS3 to
cancel its denominator, and MS4 on the two resulting composites. For two triangles choose
an X-predecessor and complete its S-map to a distinguished denominator triangle by
`lem-pur-triangle-completion-ms6-05r9`. Rotate and repeat for Y and Z. The candidate component
maps agree with the fixed maps into T. MS3 gives a further S-precomposition making the
first triangle square commute; complete this map to a denominator triangle. Rotate and
repeat for the remaining squares. Earlier equalities persist under precomposition and MS1
keeps all components in S. Iterate for a finite nonempty family; for the empty family use
the identity of T.
(2) For parallel maps, their composites with the target denominator agree. MS3 gives an
S-map into the common source equalizing their first components. Complete it to a
triangle map by `lem-pur-triangle-completion-ms6-05r9`. Rotate and repeat for the second and
third components. Precomposition preserves earlier equalities and MS1 preserves membership
in S. The final composite is the required equalizer arrow.
(3) All chosen triangles are distinguished, all component maps lie in S, and all maps
commute over T. Thus these are precisely the finite-predecessor and parallel-equalization
conditions of the category in the node. -/
theorem triangle_common_refinement_and_equalization
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : MorphismProperty C) (hS : S.IsSaturatedMultiplicativeSystem)
    [S.IsCompatibleWithTriangulation] (T : Triangle C) (hT : T ∈ distTriang C) :
    (∀ (I : Type w) [Finite I] (D : I → Triangle C) (s : ∀ i : I, D i ⟶ T),
      (∀ i : I, D i ∈ distTriang C) →
      (∀ i : I, S (s i).hom₁ ∧ S (s i).hom₂ ∧ S (s i).hom₃) →
      ∃ (U : Triangle C) (t : U ⟶ T), U ∈ distTriang C ∧
        S t.hom₁ ∧ S t.hom₂ ∧ S t.hom₃ ∧
        ∀ i : I, ∃ a : U ⟶ D i,
          S a.hom₁ ∧ S a.hom₂ ∧ S a.hom₃ ∧ a ≫ s i = t) ∧
    (∀ (D E : Triangle C) (s : D ⟶ T) (t : E ⟶ T),
      D ∈ distTriang C → E ∈ distTriang C →
      S s.hom₁ → S s.hom₂ → S s.hom₃ →
      S t.hom₁ → S t.hom₂ → S t.hom₃ →
      ∀ a b : D ⟶ E,
        S a.hom₁ → S a.hom₂ → S a.hom₃ →
        S b.hom₁ → S b.hom₂ → S b.hom₃ →
        a ≫ t = s → b ≫ t = s →
        ∃ (U : Triangle C) (r : U ⟶ T) (q : U ⟶ D), U ∈ distTriang C ∧
          S r.hom₁ ∧ S r.hom₂ ∧ S r.hom₃ ∧
          S q.hom₁ ∧ S q.hom₂ ∧ S q.hom₃ ∧ q ≫ s = r ∧
          q.hom₁ ≫ a.hom₁ = q.hom₁ ≫ b.hom₁ ∧
          q.hom₂ ≫ a.hom₂ = q.hom₂ ≫ b.hom₂ ∧
          q.hom₃ ≫ a.hom₃ = q.hom₃ ≫ b.hom₃) := by
  have : S.HasRightCalculusOfFractions := hS.1.2
  constructor
  · intro I _ D s hD hs
    obtain ⟨U, t, hU, ht, href⟩ := finite_triangle_refinement S hS T hT I D s hD hs
    refine ⟨U, t, hU, ht.1, ht.2.1, ht.2.2, ?_⟩
    intro i
    obtain ⟨a, ha, eq⟩ := href i
    exact ⟨a, ha.1, ha.2.1, ha.2.2, eq⟩
  · intro D E s t hD hE hs₁ hs₂ hs₃ ht₁ ht₂ ht₃ a b ha₁ ha₂ ha₃ hb₁ hb₂ hb₃ eas ebt
    let hst : Denom S t := ⟨ht₁, ht₂, ht₃⟩
    obtain ⟨U, q, hU, hq, heq⟩ := equalize S hS hD a b t hst (by rw [eas, ebt])
    let r := q ≫ s
    have hr : Denom S r := denom_comp S (fun _ _ => S.comp_mem _ _) hq
      ⟨hs₁, hs₂, hs₃⟩
    refine ⟨U, r, q, hU, hr.1, hr.2.1, hr.2.2, hq.1, hq.2.1, hq.2.2, ?_, ?_, ?_, ?_⟩
    · rfl
    · exact congrArg TriangleMorphism.hom₁ heq
    · exact congrArg TriangleMorphism.hom₂ heq
    · exact congrArg TriangleMorphism.hom₃ heq

end CategoryTheory
