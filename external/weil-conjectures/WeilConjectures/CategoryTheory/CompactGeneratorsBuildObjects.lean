/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.CompactGeneratorTelescopeIso

/-!
# Building objects from compact generators

Source: Stacks Project, Derived Categories, Lemma 13.37.4 (Tag 09SN)
(blueprint: lem-pc-compact-generators-build-objects).
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace CategoryTheory

private structure GeneratorStep
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{max w v} C]
    {I : Type (max w v)} (E : I → C) (Y : C) (p : Σ X : C, X ⟶ Y) where
  next : Σ X : C, X ⟶ Y
  Z : C
  a : Z ⟶ p.1
  t : p.1 ⟶ next.1
  b : next.1 ⟶ Z⟦(1 : ℤ)⟧
  shape : ∃ (J : Type (max w v)) (i : J → I) (m : J → ℤ),
    Nonempty (Z ≅ ∐ fun j : J => (E (i j))⟦m j⟧)
  distinguished : Triangle.mk a t b ∈ distTriang C
  comm : t ≫ next.2 = p.2
  kill : ∀ (i : I) (m : ℤ) (g : (E i)⟦m⟧ ⟶ p.1),
    g ≫ p.2 = 0 → g ≫ t = 0

private theorem generatorStep_exists
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{max w v} C]
    {I : Type (max w v)} (E : I → C) (Y : C) (p : Σ X : C, X ⟶ Y) :
    Nonempty (GeneratorStep E Y p) := by
  classical
  let J := Σ i : I, Σ m : ℤ, {g : (E i)⟦m⟧ ⟶ p.1 // g ≫ p.2 = 0}
  let F : J → C := fun j => (E j.1)⟦j.2.1⟧
  let a : (∐ F) ⟶ p.1 := Sigma.desc (fun j : J => j.2.2.1)
  have ha : a ≫ p.2 = 0 := by
    apply Sigma.hom_ext
    intro j
    simp only [a, Sigma.ι_comp_desc_assoc, comp_zero]
    exact j.2.2.2
  obtain ⟨X', t, b, hd⟩ := distinguished_cocone_triangle a
  obtain ⟨f', hf'⟩ := Triangle.yoneda_exact₂ _ hd p.2 ha
  refine ⟨⟨⟨X', f'⟩, ∐ F, a, t, b,
    ⟨J, fun j => j.1, fun j => j.2.1, ⟨Iso.refl _⟩⟩, hd, hf'.symm, ?_⟩⟩
  intro i m g hg
  have hat : a ≫ t = 0 := comp_distTriang_mor_zero₁₂ _ hd
  have h := congrArg (fun k => Sigma.ι F ⟨i, m, ⟨g, hg⟩⟩ ≫ k) hat
  simpa only [a, Sigma.ι_comp_desc_assoc, comp_zero] using h

/-- Every object is the sequential homotopy colimit of a sequence built from coproducts
of shifts of compact generators (Stacks, Tag 09SN)
(blueprint: lem-pc-compact-generators-build-objects).

For the proof, start with the coproduct of all shifted generators mapping to `Y`.
At each stage take the coproduct of all shifted generators mapping to the current
object whose composites to `Y` vanish, and complete its map to a distinguished
triangle. Exactness gives compatible maps from the successive objects to `Y`.
Their coproduct map vanishes on identity minus shift, so it factors through the
homotopy colimit. Complete that map to a triangle with cone `C`. Compactness
lets every map from a shifted generator to the telescope factor through a stage;
the next triangle kills it. Exactness then lifts any map from a shifted generator
to `C` to a shifted map into `Y`. This map occurs among the summands at the first
stage, so its image in `C` is zero. Generation forces `C` to be zero, making the
telescope map an isomorphism; transport the telescope triangle along it. -/
theorem compactGenerators_buildObjects
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{max w v} C]
    {I : Type (max w v)} (E : I → C)
    (hcompact : ∀ i : I, IsCompactObject (E i))
    (hgenerate : IsTriangulatedGeneratingFamily E) (Y : C) :
    ∃ (X : ℕ → C) (t : ∀ n : ℕ, X n ⟶ X (n + 1)),
      (∃ (J : Type (max w v)) (i : J → I) (m : J → ℤ),
        Nonempty (X 0 ≅ ∐ fun j : J => (E (i j))⟦m j⟧)) ∧
      (∃ (Z : ℕ → C) (a : ∀ n : ℕ, Z n ⟶ X n)
          (b : ∀ n : ℕ, X (n + 1) ⟶ (Z n)⟦(1 : ℤ)⟧),
        (∀ n : ℕ, ∃ (J : Type (max w v)) (i : J → I) (m : J → ℤ),
          Nonempty (Z n ≅ ∐ fun j : J => (E (i j))⟦m j⟧)) ∧
        ∀ n : ℕ, Triangle.mk (a n) (t n) (b n) ∈ distTriang C) ∧
      ∃ (q : (∐ fun n : ULift.{max w v} ℕ => X n.down) ⟶ Y)
          (r : Y ⟶ (∐ fun n : ULift.{max w v} ℕ => X n.down)⟦(1 : ℤ)⟧),
        Triangle.mk
          (𝟙 (∐ fun n : ULift.{max w v} ℕ => X n.down) -
            Sigma.desc (fun n : ULift.{max w v} ℕ =>
              t n.down ≫ Sigma.ι (fun k : ULift.{max w v} ℕ => X k.down)
                ⟨n.down + 1⟩))
          q r ∈ distTriang C := by
  classical
  let J := Σ i : I, Σ m : ℤ, (E i)⟦m⟧ ⟶ Y
  let F : J → C := fun j => (E j.1)⟦j.2.1⟧
  let f₀ : (∐ F) ⟶ Y := Sigma.desc (fun j : J => j.2.2)
  let step := fun p : Σ X : C, X ⟶ Y =>
    Classical.choice (generatorStep_exists E Y p)
  let p : ℕ → (Σ X : C, X ⟶ Y) := fun n =>
    Nat.rec ⟨∐ F, f₀⟩ (fun _ p => (step p).next) n
  let X := fun n => (p n).1
  let t := fun n => (step (p n)).t
  have hcomm (n : ℕ) : t n ≫ (p (n + 1)).2 = (p n).2 :=
    (step (p n)).comm
  have hstart (i : I) (m : ℤ) (g : (E i)⟦m⟧ ⟶ Y) :
      ∃ a : (E i)⟦m⟧ ⟶ X 0, a ≫ (p 0).2 = g := by
    exact ⟨Sigma.ι F ⟨i, m, g⟩, Sigma.ι_comp_desc _ _⟩
  have hkill (n : ℕ) (i : I) (m : ℤ) (g : (E i)⟦m⟧ ⟶ X n)
      (hg : g ≫ (p n).2 = 0) : g ≫ t n = 0 :=
    (step (p n)).kill i m g hg
  refine ⟨X, t, ⟨J, fun j => j.1, fun j => j.2.1, ⟨Iso.refl _⟩⟩,
    ⟨fun n => (step (p n)).Z, fun n => (step (p n)).a,
      fun n => (step (p n)).b, fun n => (step (p n)).shape,
      fun n => (step (p n)).distinguished⟩, ?_⟩
  let A := fun n : ULift.{max w v} ℕ => X n.down
  let s : (∐ A) ⟶ ∐ A := Sigma.desc (fun n : ULift.{max w v} ℕ =>
    t n.down ≫ Sigma.ι A ⟨n.down + 1⟩)
  obtain ⟨H, q, r, hd⟩ := distinguished_cocone_triangle (𝟙 (∐ A) - s)
  let f : (∐ A) ⟶ Y := Sigma.desc (fun n => (p n.down).2)
  have hf : (𝟙 (∐ A) - s) ≫ f = 0 := by
    apply Sigma.hom_ext
    intro n
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp,
      comp_zero, s, f, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.assoc]
    exact sub_eq_zero.mpr (hcomm n.down).symm
  obtain ⟨c, hc⟩ := Triangle.yoneda_exact₂ _ hd f hf
  change f = q ≫ c at hc
  have hstage (n : ℕ) : Sigma.ι A ⟨n⟩ ≫ q ≫ c = (p n).2 := by
    rw [← hc]
    exact Sigma.ι_comp_desc _ _
  have : IsIso c := compactGenerator_telescope_isIso E hcompact hgenerate
    Y X t (fun n => (p n).2) hstart hkill H q r hd c hstage
  refine ⟨q ≫ c, inv c ≫ r, ?_⟩
  refine isomorphic_distinguished _ hd _ ?_
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso c).symm
    (by simp [A, s]) (by simp) (by simp)

end CategoryTheory
