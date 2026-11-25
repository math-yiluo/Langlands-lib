/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Compact objects form a thick subcategory

Source: Stacks Project, Derived Categories, Lemma 13.37.2 (Tag 09QH)
(blueprint: lem-sc-compact-objects-thick).
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- Integer shifts preserve compactness.
Source: Stacks Project, Tag 09QH (blueprint: lem-sc-compact-cone).
Proof: conjugate the compact-Hom comparison by the additive Hom equivalences of
shift and inverse shift, using the inverse-shift coproduct comparison. -/
theorem compact_shift {C : Type u} [Category.{v} C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [HasCoproducts.{w} C]
    (K : C) (hK : IsCompactObject K) (n : ℤ) :
    IsCompactObject (K⟦n⟧) := by
  classical
  intro J A
  let e := shiftEquiv C n
  have : e.functor.Additive := inferInstanceAs (shiftFunctor C n).Additive
  have : e.inverse.Additive := inferInstanceAs (shiftFunctor C (-n)).Additive
  let adj := e.toAdjunction
  let D := DirectSum.congrAddEquiv (fun j ↦ adj.homAddEquiv K (A j))
  let s := sigmaComparison e.inverse A
  let post : (K ⟶ e.inverse.obj (∐ A)) ≃+ (K ⟶ ∐ fun j ↦ e.inverse.obj (A j)) :=
    { toEquiv := Iso.homCongr (Iso.refl K) (asIso s).symm
      map_add' := by
        intro f g
        simp [Iso.homCongr, Preadditive.add_comp] }
  let Q := (adj.homAddEquiv K (∐ A)).trans post
  let φ := DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp (e.functor.obj K) (Sigma.ι A j))
  let ψ := DirectSum.toAddMonoid
    (fun j ↦ Preadditive.rightComp K (Sigma.ι (fun j ↦ e.inverse.obj (A j)) j))
  have hcomm : Q.toAddMonoidHom.comp φ = ψ.comp D.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro j f
    change Q (φ (DirectSum.of _ j f)) = ψ (D (DirectSum.of _ j f))
    have hφof : φ (DirectSum.of _ j f) = f ≫ Sigma.ι A j :=
      DirectSum.toAddMonoid_of
        (fun j ↦ Preadditive.rightComp (e.functor.obj K) (Sigma.ι A j)) j f
    have hDof : D (DirectSum.of _ j f) =
        DirectSum.of _ j (adj.homAddEquiv K (A j) f) :=
      DirectSum.map_of (fun j ↦ (adj.homAddEquiv K (A j)).toAddMonoidHom) j f
    rw [hφof, hDof]
    rw [show ψ (DirectSum.of _ j (adj.homAddEquiv K (A j) f)) =
        adj.homAddEquiv K (A j) f ≫ Sigma.ι (fun j ↦ e.inverse.obj (A j)) j from
      DirectSum.toAddMonoid_of
        (fun j ↦ Preadditive.rightComp K (Sigma.ι (fun j ↦ e.inverse.obj (A j)) j)) j _]
    dsimp [Q, post, Iso.homCongr]
    rw [Category.id_comp]
    change adj.homEquiv K (∐ A) (f ≫ Sigma.ι A j) ≫ inv s =
      adj.homEquiv K (A j) f ≫ Sigma.ι (fun j ↦ e.inverse.obj (A j)) j
    rw [adj.homEquiv_naturality_right, Category.assoc]
    rw [map_ι_comp_inv_sigmaComparison]
  have hψ := hK J (fun j ↦ e.inverse.obj (A j))
  have hφ : Function.Bijective (fun x ↦ Q (φ x)) := by
    have hh : (fun x ↦ Q (φ x)) = (fun x ↦ ψ (D x)) :=
      funext (fun x ↦ DFunLike.congr_fun hcomm x)
    rw [hh]
    exact hψ.comp D.bijective
  constructor
  · intro x y hxy
    exact hφ.1 (congrArg Q hxy)
  · intro f
    obtain ⟨x, hx⟩ := hφ.2 (Q f)
    exact ⟨x, Q.injective hx⟩

open Classical in
/-- The compact-Hom comparison is natural in its source.
Source: Stacks Project, Tag 09QH (blueprint: lem-sc-compact-cone).
Proof: evaluate on a single direct-sum component and use composition associativity. -/
theorem compact_comparison_naturality
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {K L : C} (s : K ⟶ L) {J : Type w} (A : J → C) :
    (DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp K (Sigma.ι A j))).comp
        (DirectSum.map (fun j ↦ Preadditive.leftComp (A j) s)) =
      (Preadditive.leftComp (∐ A) s).comp
        (DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp L (Sigma.ι A j))) := by
  classical
  apply DirectSum.addHom_ext
  intro j f
  simp only [AddMonoidHom.comp_apply, DirectSum.map_of, DirectSum.toAddMonoid_of]
  exact (Category.assoc s f (Sigma.ι A j))

open Classical in
private theorem directSum_exact
    {J : Type w} {A B D : J → Type v}
    [∀ j, AddCommGroup (A j)] [∀ j, AddCommGroup (B j)] [∀ j, AddCommGroup (D j)]
    (f : ∀ j, A j →+ B j) (g : ∀ j, B j →+ D j)
    (h : ∀ j, Function.Exact (f j) (g j)) :
    Function.Exact (DirectSum.map f) (DirectSum.map g) := by
  intro x
  constructor
  · intro hx
    have hxj (j : J) : g j (x j) = 0 := by
      have h' := congrArg (fun y ↦ y j) hx
      simpa only [DirectSum.map_apply, DFinsupp.zero_apply] using h'
    choose y hy using fun j ↦ (h j (x j)).mp (hxj j)
    refine ⟨∑ j ∈ x.support, DirectSum.of A j (y j), ?_⟩
    simp only [map_sum, DirectSum.map_of, hy]
    exact DirectSum.sum_support_of x
  · rintro ⟨y, rfl⟩
    ext j
    simpa only [DirectSum.map_apply, DFinsupp.zero_apply] using (h j).apply_apply_eq_zero (y j)

private theorem triangle_hom_exact
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) (A : C) :
    Function.Exact (Preadditive.leftComp A T.mor₂) (Preadditive.leftComp A T.mor₁) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := T.yoneda_exact₂ hT x hx
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    change T.mor₁ ≫ T.mor₂ ≫ y = 0
    rw [← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]

/-- The third term of a distinguished triangle of compact objects is compact.
Source: Stacks Project, Derived Categories, Lemma 13.37.2, Tag 09QH.
(blueprint: lem-sc-compact-cone).

Proof: apply Hom(-,A_j) to the triangle and to its rotations. The resulting
five-term exact sequences have the five Hom groups from Y[1], X[1], Z, Y, X.
Take their direct sum over j; it remains exact since direct sums of abelian groups
are exact. Compare with Hom(-,the coproduct of A_j) using the canonical compactness
maps. Naturality makes the diagram commute. The outer four comparison maps are
bijective because X and Y and their shifts are compact. The five lemma proves
bijectivity for Z, for every family A_j, hence Z is compact. -/
theorem compact_cone
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [HasCoproducts.{w} C]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsCompactObject T.obj₁) (h₂ : IsCompactObject T.obj₂) :
    IsCompactObject T.obj₃ := by
  classical
  intro J A
  let U := T.rotate
  let V := U.rotate
  have hU : U ∈ distTriang C := rot_of_distTriang T hT
  have hV : V ∈ distTriang C := rot_of_distTriang U hU
  let c (K : C) := DirectSum.toAddMonoid
    (fun j ↦ Preadditive.rightComp K (Sigma.ι A j))
  let d (s : C) (t : C) (f : s ⟶ t) :=
    DirectSum.map (fun j ↦ Preadditive.leftComp (A j) f)
  let p (s : C) (t : C) (f : s ⟶ t) := Preadditive.leftComp (∐ A) f
  have hc {s t : C} (f : s ⟶ t) : (p s t f).comp (c t) = (c s).comp (d s t f) :=
    (compact_comparison_naturality f A).symm
  have hd₁ : Function.Exact (d _ _ V.mor₂) (d _ _ V.mor₁) :=
    directSum_exact _ _ (fun j ↦ triangle_hom_exact V hV (A j))
  have hd₂ : Function.Exact (d _ _ U.mor₂) (d _ _ U.mor₁) :=
    directSum_exact _ _ (fun j ↦ triangle_hom_exact U hU (A j))
  have hd₃ : Function.Exact (d _ _ T.mor₂) (d _ _ T.mor₁) :=
    directSum_exact _ _ (fun j ↦ triangle_hom_exact T hT (A j))
  have hp₁ := triangle_hom_exact V hV (∐ A)
  have hp₂ := triangle_hom_exact U hU (∐ A)
  have hp₃ := triangle_hom_exact T hT (∐ A)
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (d _ _ V.mor₂) (d _ _ T.mor₃) (d _ _ T.mor₂) (d _ _ T.mor₁)
    (p _ _ V.mor₂) (p _ _ T.mor₃) (p _ _ T.mor₂) (p _ _ T.mor₁)
    (c (T.obj₂⟦(1 : ℤ)⟧)) (c (T.obj₁⟦(1 : ℤ)⟧)) (c T.obj₃)
    (c T.obj₂) (c T.obj₁)
    (hc V.mor₂) (hc T.mor₃) (hc T.mor₂) (hc T.mor₁)
    hd₁ hd₂ hd₃ hp₁ hp₂ hp₃
    (compact_shift T.obj₂ h₂ (1 : ℤ) J A).2
    (compact_shift T.obj₁ h₁ (1 : ℤ) J A)
    (h₂ J A) (h₁ J A).1

end CategoryTheory
