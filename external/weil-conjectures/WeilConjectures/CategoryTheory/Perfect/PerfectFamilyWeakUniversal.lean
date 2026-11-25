/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.CategoryTheory.Perfect.PerfectFamilyTelescope
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-! # Weakly universal elements from a perfect family

Source: Krause, Derived categories, resolutions, and Brown representability, Section 4.5.
(blueprint: lem-sfb-perfect-family-weak-universal)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

open CategoryTheory.Pretriangulated CategoryTheory.BrownRepresentability
open ZeroObject

section PerfectFamily

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {J : Type v} (S : J → C)

private theorem solutionSet_cohomological
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological] : IsCohomological H := by
  intro T hT x hx
  exact (ShortComplex.ab_exact_iff _).1 (H.map_distinguished_op_exact T hT) x hx

omit [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
private theorem solutionSet_products
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H) :
    SendsCoproductsToProducts H := by
  intro I X c hc x
  have := hH I
  let F := H ⋙ forget AddCommGrpCat
  have hl : IsLimit (F.mapCone c.op) := isLimitOfPreserves F (Cofan.IsColimit.op hc)
  let s : ∀ i : Discrete I, (Discrete.functor (fun i ↦ op (X i)) ⋙ F).obj i :=
    fun i ↦ x i.as
  have hs : s ∈ (Discrete.functor (fun i ↦ op (X i)) ⋙ F).sections := by
    intro i j f
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    obtain rfl := Discrete.eq_of_hom f
    simp
  obtain ⟨y, hy, hu⟩ := (Types.isLimit_iff _).1 ⟨hl⟩ s hs
  refine ⟨y, fun i ↦ hy ⟨i⟩, ?_⟩
  intro z hz
  exact hu z (fun i ↦ hz i.as)

variable [HasCoproducts.{v} C]

private theorem solutionSet_step
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : SendsCoproductsToProducts H) (X : C) (x : H.obj (op X)) :
    ∃ (Y : C) (y : H.obj (op Y)) (a : X ⟶ Y), H.map a.op y = x ∧
      ∀ j (f : S j ⟶ X), H.map f.op x = 0 → f ≫ a = 0 := by
  classical
  let K := Σ j, {f : S j ⟶ X // H.map f.op x = 0}
  let F : K → C := fun k ↦ S k.1
  let κ : (∐ F) ⟶ X := Sigma.desc fun k ↦ k.2.val
  obtain ⟨Y, a, δ, hT⟩ := distinguished_cocone_triangle κ
  have hκ : H.map κ.op x = 0 := by
    obtain ⟨z, hz, hu⟩ := hH _ (coproductIsCoproduct F) (fun _ ↦ 0)
    apply (hu _ ?_).trans (hu 0 (fun _ ↦ map_zero _)).symm
    intro k
    change H.map (Sigma.ι F k).op (H.map κ.op x) = 0
    rw [← map_comp_apply]
    simpa [κ] using k.2.property
  obtain ⟨y, hy⟩ := solutionSet_cohomological H _ hT x hκ
  refine ⟨Y, y, a, hy, ?_⟩
  intro j f hf
  have h := comp_distTriang_mor_zero₁₂ (Triangle.mk κ a δ) hT
  change κ ≫ a = 0 at h
  have hi := congrArg (fun z ↦ Sigma.ι F ⟨j, f, hf⟩ ≫ z) h
  simpa only [κ, Sigma.ι_comp_desc_assoc, comp_zero] using hi

private theorem solutionSet_approximation
    (hshift : ∀ (j : J) (n : ℤ), ∃ k, Nonempty (S k ≅ (S j)⟦n⟧))
    (hperfect : ∀ (I : Type v) (X Y : I → C) (f : ∀ i, X i ⟶ Y i),
      (∀ i j, Function.Surjective (fun g : S j ⟶ X i ↦ g ≫ f i)) →
      ∀ j, Function.Surjective (fun g : S j ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f))
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H)
    (W : C) (w : H.obj (op W)) :
    ∃ (X : C) (x : H.obj (op X)) (j : W ⟶ X), H.map j.op x = w ∧
      ∀ i, Function.Bijective (fun f : S i ⟶ X ↦ H.map f.op x) := by
  classical
  have hprod := solutionSet_products H hH
  let K := Σ j, H.obj (op (S j))
  let F : K → C := fun k ↦ S k.1
  obtain ⟨y, hy, _⟩ := hprod _ (coproductIsCoproduct F) (fun k ↦ k.2)
  let X₀ := W ⊞ ∐ F
  let x₀ : H.obj (op X₀) := H.map biprod.fst.op w + H.map biprod.snd.op y
  choose next elt a ha hkill using solutionSet_step S H hprod
  let stage : ℕ → Σ X : C, H.obj (op X) :=
    fun n ↦ Nat.rec ⟨X₀, x₀⟩ (fun _ p ↦ ⟨next p.1 p.2, elt p.1 p.2⟩) n
  let X : ℕ → C := fun n ↦ (stage n).1
  let t : ∀ n, X n ⟶ X (n + 1) := fun n ↦ a (stage n).1 (stage n).2
  obtain ⟨T, q, r, hT⟩ :=
    distinguished_cocone_triangle (𝟙 (Telescope.sum X) - Telescope.shift X t)
  obtain ⟨z, hz⟩ := Telescope.exists_lift hT H (solutionSet_cohomological H) hprod
    (fun n ↦ (stage n).2) (fun n ↦ ha _ _)
  have hs : ∀ i, Function.Surjective (fun f : S i ⟶ X 0 ↦ H.map f.op (stage 0).2) := by
    intro i b
    refine ⟨Sigma.ι F ⟨i, b⟩ ≫ biprod.inr, ?_⟩
    change H.map (Sigma.ι F ⟨i, b⟩ ≫ biprod.inr).op x₀ = b
    rw [map_comp_apply]
    dsimp [x₀]
    rw [map_add, ← map_comp_apply, ← map_comp_apply]
    simp only [biprod.inr_fst, op_zero, H.map_zero, AddCommGrpCat.zero_apply,
      biprod.inr_snd, op_id, H.map_id, AddCommGrpCat.id_apply, zero_add]
    exact hy ⟨i, b⟩
  have hb := perfectFamily_telescope_bijective S hshift hperfect H X t
    (fun n ↦ (stage n).2) (fun n ↦ ha _ _) hs
    (fun n i f hf ↦ hkill _ _ i f hf) T q r hT z hz
  refine ⟨T, z, biprod.inl ≫ Telescope.ι X 0 ≫ q, ?_, hb⟩
  rw [map_comp_apply]
  have hz0 : H.map (Telescope.ι X 0 ≫ q).op z = x₀ := hz 0
  refine (congrArg (H.map (biprod.inl : W ⟶ X₀).op) hz0).trans ?_
  dsimp [x₀]
  rw [map_add, ← map_comp_apply, ← map_comp_apply]
  simp

omit [HasCoproducts.{v} C] in
private theorem solutionSet_universal_iso
    (hshift : ∀ (j : J) (n : ℤ), ∃ k, Nonempty (S k ≅ (S j)⟦n⟧))
    (hzero : ∀ X : C, (∀ j (f : S j ⟶ X), f = 0) → IsZero X)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) {X Y : C}
    {x : H.obj (op X)} {y : H.obj (op Y)}
    (hx : ∀ i, Function.Bijective (fun f : S i ⟶ X ↦ H.map f.op x))
    (hy : ∀ i, Function.Bijective (fun f : S i ⟶ Y ↦ H.map f.op y))
    (g : X ⟶ Y) (hg : H.map g.op y = x) : IsIso g := by
  have hbij : ∀ i, Function.Bijective (fun f : S i ⟶ X ↦ f ≫ g) := by
    intro i
    refine (Function.Bijective.of_comp_iff' (hy i) _).1 ?_
    convert hx i using 1
    ext f
    simp only [Function.comp_apply, map_comp_apply, hg]
  obtain ⟨Z, p, δ, hT⟩ := distinguished_cocone_triangle g
  apply (Triangle.isZero₃_iff_isIso₁ _ hT).1
  apply hzero
  intro i f
  obtain ⟨j, ⟨e⟩⟩ := hshift i (-1)
  have h₁ : f ≫ δ = 0 := by
    refine eq_zero_of_comp_shift_eq_zero e g (fun f' hf' ↦ (hbij j).1 ?_) _ ?_
    · simpa using hf'
    · have h : δ ≫ g⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
      rw [Category.assoc, h, comp_zero]
  obtain ⟨f', rfl⟩ := Triangle.coyoneda_exact₃ _ hT f h₁
  obtain ⟨f'', rfl⟩ := (hbij i).2 f'
  have h : g ≫ p = 0 := comp_distTriang_mor_zero₁₂ _ hT
  simp [h]

end PerfectFamily

/-- A shift-closed perfect family detecting zero objects gives a single weakly
universal pair for every cohomological functor that sends coproducts to products.

Source: Krause, *Derived categories, resolutions, and Brown representability*,
Section 4.5, the cellular proof of Brown representability.
(blueprint: lem-sfb-perfect-family-weak-universal)

Proof: for each initial pair (W,w), adjoin the coproduct of all pairs (S_j,z).
At every subsequent stage take the cone of the evaluation coproduct of generator
maps annihilated by the current element. Product preservation and cohomological
exactness lift that element to the next stage. Take the sequential telescope and
lift the compatible elements; the perfect-family telescope calculation makes the
resulting element universal on every S_j. Start with W=0 to obtain (X,x). For an
arbitrary (Y,y), repeat the construction starting at X plus Y. The resulting map
from X to the new telescope preserves elements and is bijective on Hom from S_j.
Its cone is zero by shift closure, triangle exactness, and zero detection, so the
map is invertible. Composing the map from Y with its inverse pulls x back to y.
-/
theorem perfectFamily_exists_weakUniversal
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [HasCoproducts.{v} C]
    {J : Type v} (S : J → C)
    (hshift : ∀ (j : J) (n : ℤ), ∃ k, Nonempty (S k ≅ (S j)⟦n⟧))
    (hzero : ∀ X : C, (∀ j (f : S j ⟶ X), f = 0) → IsZero X)
    (hperfect : ∀ (I : Type v) (X Y : I → C) (f : ∀ i, X i ⟶ Y i),
      (∀ i j, Function.Surjective (fun g : S j ⟶ X i ↦ g ≫ f i)) →
      ∀ j, Function.Surjective (fun g : S j ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f))
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H) :
    ∃ (X : C) (x : H.obj (op X)),
      ∀ (Y : C) (y : H.obj (op Y)), ∃ f : Y ⟶ X, H.map f.op x = y := by
  obtain ⟨X, x, _, _, hx⟩ := solutionSet_approximation S hshift hperfect H hH 0 0
  refine ⟨X, x, ?_⟩
  intro Y y
  let w : H.obj (op (X ⊞ Y)) := H.map biprod.fst.op x + H.map biprod.snd.op y
  obtain ⟨T, t, j, hj, ht⟩ := solutionSet_approximation S hshift hperfect H hH (X ⊞ Y) w
  have hi : H.map (biprod.inl ≫ j).op t = x := by
    rw [map_comp_apply, hj]
    dsimp [w]
    rw [map_add, ← map_comp_apply, ← map_comp_apply]
    simp
  have : IsIso (biprod.inl ≫ j) := solutionSet_universal_iso S hshift hzero H hx ht _ hi
  refine ⟨biprod.inr ≫ j ≫ inv (biprod.inl ≫ j), ?_⟩
  have hinv : H.map (inv (biprod.inl ≫ j)).op x = t := by
    rw [← hi, ← map_comp_apply, IsIso.inv_hom_id]
    simp
  rw [map_comp_apply, map_comp_apply, hinv, hj]
  dsimp [w]
  rw [map_add, ← map_comp_apply, ← map_comp_apply]
  simp

end CategoryTheory
