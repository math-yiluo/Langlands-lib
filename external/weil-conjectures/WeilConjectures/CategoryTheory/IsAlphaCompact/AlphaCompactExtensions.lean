/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.AlphaCompactObject
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.IsAlphaCompact.AlphaCompactObjectProperties
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-! # Extension closure of Krause alpha-compactness

Source: Krause (2001), Lemma 5, page 124.
(blueprint: lem-sfb-alpha-compact-extensions)
-/

@[expose] public section

universe v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite ZeroObject
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasCoproducts.{v} C]

-- The opposite-product argument is also used in PerfectFamilyTelescope.
omit [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
private theorem sum_map_op {I : Type v} (X Y : I → C) (f : ∀ i, X i ⟶ Y i) :
    (Limits.Sigma.map f).op ≫ (opCoproductIsoProduct X).hom =
      (opCoproductIsoProduct Y).hom ≫ Limits.Pi.map (fun i ↦ (f i).op) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, opCoproductIsoProduct_hom_comp_π, Pi.map_π]
  rw [← op_comp, Limits.Sigma.ι_map, op_comp]
  rw [← Category.assoc, opCoproductIsoProduct_hom_comp_π]

private theorem sum_weak_kernel {I : Type v} (T : I → Triangle C)
    (hT : ∀ i, T i ∈ distTriang C) {W : C}
    (f : W ⟶ ∐ fun i ↦ (T i).obj₂)
    (hf : f ≫ Limits.Sigma.map (fun i ↦ (T i).mor₂) = 0) :
    ∃ g : W ⟶ ∐ fun i ↦ (T i).obj₁,
      g ≫ Limits.Sigma.map (fun i ↦ (T i).mor₁) = f := by
  let U : I → Triangle Cᵒᵖ := fun i ↦ (triangleOpEquivalence C).functor.obj (op (T i))
  have hU : ∀ i, U i ∈ distTriang Cᵒᵖ := fun i ↦ op_distinguished (T i) (hT i)
  let V := productTriangle U
  have hV : V ∈ distTriang Cᵒᵖ := productTriangle_distinguished U hU
  let e₁ := opCoproductIsoProduct (fun i ↦ (T i).obj₁)
  let e₂ := opCoproductIsoProduct (fun i ↦ (T i).obj₂)
  let e₃ := opCoproductIsoProduct (fun i ↦ (T i).obj₃)
  let α : V.obj₂ ⟶ op W := e₂.inv ≫ f.op
  have hα : V.mor₁ ≫ α = 0 := by
    have h := sum_map_op (fun i ↦ (T i).obj₂) (fun i ↦ (T i).obj₃)
      (fun i ↦ (T i).mor₂)
    change (Limits.Sigma.map (fun i ↦ (T i).mor₂)).op ≫ e₂.hom =
      e₃.hom ≫ V.mor₁ at h
    apply (cancel_epi e₃.hom).1
    change e₃.hom ≫ (V.mor₁ ≫ (e₂.inv ≫ f.op)) = e₃.hom ≫ 0
    rw [comp_zero, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_assoc,
      ← op_comp, hf, op_zero]
  obtain ⟨γ, hγ⟩ := Triangle.yoneda_exact₂ V hV α hα
  refine ⟨(e₁.hom ≫ γ).unop, ?_⟩
  apply Quiver.Hom.op_inj
  rw [op_comp, Quiver.Hom.op_unop]
  have h := sum_map_op (fun i ↦ (T i).obj₁) (fun i ↦ (T i).obj₂)
    (fun i ↦ (T i).mor₁)
  change (Limits.Sigma.map (fun i ↦ (T i).mor₁)).op ≫ e₁.hom =
    e₂.hom ≫ V.mor₂ at h
  rw [← Category.assoc, h, Category.assoc, ← hγ]
  simp [α]

private def FactorsOut (H : ObjectProperty C) (U : C) : Prop :=
  ∀ (I : Type v) (Y : I → C) (f : U ⟶ ∐ Y),
    ∃ Z : I → C, (∀ i, H (Z i)) ∧
      ∃ (a : ∀ i, Z i ⟶ Y i) (g : U ⟶ ∐ Z), g ≫ Limits.Sigma.map a = f

private theorem factorsOut_cone
    (H : ObjectProperty C) [H.IsTriangulated] [H.IsClosedUnderIsomorphisms]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (hU : FactorsOut H T.obj₁) (hV : FactorsOut H T.obj₂)
    (hU' : FactorsOut H (T.obj₁⟦(1 : ℤ)⟧)) : FactorsOut H T.obj₃ := by
  classical
  intro I Y f
  obtain ⟨V, hV, a, g, hg⟩ := hV I Y (T.mor₂ ≫ f)
  choose F k δ hF using fun i ↦ distinguished_cocone_triangle₁ (a i)
  let R : I → Triangle C := fun i ↦ Triangle.mk (k i) (a i) (δ i)
  have hz : (T.mor₁ ≫ g) ≫ Limits.Sigma.map a = 0 := by
    rw [Category.assoc, hg, ← Category.assoc, comp_distTriang_mor_zero₁₂ _ hT,
      zero_comp]
  obtain ⟨l, hl⟩ := sum_weak_kernel R hF (T.mor₁ ≫ g) hz
  obtain ⟨U, hU, b, q, hq⟩ := hU I F l
  let d (i : I) : U i ⟶ V i := b i ≫ k i
  have hcomm : T.mor₁ ≫ g = q ≫ Limits.Sigma.map d := by
    rw [← hl, ← hq, Category.assoc, Limits.Sigma.map_comp_map]
    rfl
  choose W hW c e hWtri using fun i ↦
    H.distinguished_cocone_triangle (d i) (hU i) (hV i)
  let j : (∐ V) ⟶ ∐ W := Limits.Sigma.map c
  have hj : Limits.Sigma.map d ≫ j = 0 := by
    have hz' (i : I) : d i ≫ c i = 0 := comp_distTriang_mor_zero₁₂ _ (hWtri i)
    change Limits.Sigma.map d ≫ Limits.Sigma.map c = 0
    rw [Limits.Sigma.map_comp_map]
    apply Sigma.hom_ext
    intro i
    simp only [Limits.Sigma.ι_map, hz', zero_comp, comp_zero]
  obtain ⟨K, r, s, hK⟩ := distinguished_cocone_triangle (Limits.Sigma.map d)
  let TK := Triangle.mk (Limits.Sigma.map d) r s
  obtain ⟨t, ht⟩ := TK.yoneda_exact₂ hK j hj
  obtain ⟨z, hz, _⟩ := complete_distinguished_triangle_morphism T TK hT hK q g hcomm
  let p : T.obj₃ ⟶ ∐ W := z ≫ t
  have hp : T.mor₂ ≫ p = g ≫ j := by
    dsimp [p]
    rw [← Category.assoc, hz, Category.assoc, ← ht]
  have hd (i : I) : d i ≫ a i = 0 := by
    dsimp [d]
    have hz' : k i ≫ a i = 0 := comp_distTriang_mor_zero₁₂ _ (hF i)
    rw [Category.assoc, hz', comp_zero]
  choose w hw using fun i ↦
    (Triangle.mk (d i) (c i) (e i)).yoneda_exact₂ (hWtri i) (a i) (hd i)
  change ∀ i, a i = c i ≫ w i at hw
  change ∀ i, W i ⟶ Y i at w
  have hc : j ≫ Limits.Sigma.map w = Limits.Sigma.map a := by
    apply Sigma.hom_ext
    intro i
    simp only [j, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_map]
    rw [← Category.assoc, ← hw]
  have hres : T.mor₂ ≫ (f - p ≫ Limits.Sigma.map w) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hp, Category.assoc, hc, hg, sub_self]
  obtain ⟨l', hl'⟩ := T.yoneda_exact₃ hT _ hres
  obtain ⟨Z, hZ, a', q', hq'⟩ := hU' I Y l'
  let E (i : I) := W i ⊞ Z i
  let b' (i : I) : E i ⟶ Y i := biprod.desc (w i) (a' i)
  let g' : T.obj₃ ⟶ ∐ E :=
    p ≫ Limits.Sigma.map (fun i ↦ biprod.inl : ∀ i, W i ⟶ E i) +
      T.mor₃ ≫ q' ≫ Limits.Sigma.map (fun i ↦ biprod.inr : ∀ i, Z i ⟶ E i)
  refine ⟨E, fun i ↦ H.ext_of_isTriangulatedClosed₂ _
    (binaryBiproductTriangle_distinguished (W i) (Z i)) (hW i) (hZ i), b', g', ?_⟩
  have hi : Limits.Sigma.map (fun i ↦ biprod.inl : ∀ i, W i ⟶ E i) ≫
      Limits.Sigma.map b' = Limits.Sigma.map w := by
    rw [Limits.Sigma.map_comp_map]
    simp only [b', biprod.inl_desc]
  have hr : Limits.Sigma.map (fun i ↦ biprod.inr : ∀ i, Z i ⟶ E i) ≫
      Limits.Sigma.map b' = Limits.Sigma.map a' := by
    rw [Limits.Sigma.map_comp_map]
    simp only [b', biprod.inr_desc]
  simp only [g', Preadditive.add_comp, Category.assoc, hi, hr, hq']
  change p ≫ Limits.Sigma.map w + T.mor₃ ≫ l' = f
  rw [← hl']
  abel

/-- Extensions of alpha-compact objects are alpha-compact.
Source: Krause (2001), Lemma 5, page 124, preservation of (G4) under triangles.
(blueprint: lem-sfb-alpha-compact-extensions)

Proof: form the finite extension closure H of the canonical alpha-compact class.
It is shift closed and triangulated, and all its objects are alpha-small.
Induct on the extension length to factor maps through coproducts of H-objects.
For the cone step, factor the restriction to the second vertex, take component
fiber triangles, and lift the first vertex into their coproduct. Factor this
lift and complete a square of triangles. The discrepancy factors through the
shifted first vertex and is absorbed by a componentwise binary sum.
Thus H satisfies (G4), so maximality puts H in the canonical class. -/
theorem IsAlphaCompact.extension [IsTriangulated C]
    (α : Cardinal.{v}) [Fact α.IsRegular] (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsAlphaCompact T.obj₁ α) (h₃ : IsAlphaCompact T.obj₃ α) :
    IsAlphaCompact T.obj₂ α := by
  let S := alphaCompactObjects C α
  have : S.IsClosedUnderIsomorphisms := inferInstanceAs
    (alphaCompactObjects C α).IsClosedUnderIsomorphisms
  have : ∀ n, (S.extensionProductIter n).IsClosedUnderIsomorphisms := by
    intro n
    cases n with
    | zero => exact inferInstanceAs S.IsClosedUnderIsomorphisms
    | succ n => rw [S.extensionProductIter_succ]; infer_instance
  have : S.ContainsZero := ⟨0, isZero_zero C, isAlphaCompact_zero α⟩
  have : S.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨fun X hX ↦ hX.shift n⟩⟩
  let H : ObjectProperty C := ⨆ n : ℕ, S.extensionProductIter n
  have hSH : S ≤ H := le_iSup (fun n ↦ S.extensionProductIter n) 0
  have : H.IsClosedUnderIsomorphisms := inferInstanceAs
    (⨆ n : ℕ, S.extensionProductIter n).IsClosedUnderIsomorphisms
  have : H.ContainsZero := ⟨0, isZero_zero C, hSH _ (isAlphaCompact_zero α)⟩
  have : H.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨by
    intro X hX
    obtain ⟨m, hm⟩ := (ObjectProperty.prop_iSup_iff _ _).mp hX
    exact (ObjectProperty.prop_iSup_iff _ _).mpr
      ⟨m, (S.extensionProductIter m).le_shift n X hm⟩⟩⟩
  have : H.IsTriangulatedClosed₂ := .mk' (by
    intro T hT h₁ h₃
    obtain ⟨n, hn⟩ := (ObjectProperty.prop_iSup_iff _ _).mp h₁
    obtain ⟨m, hm⟩ := (ObjectProperty.prop_iSup_iff _ _).mp h₃
    apply (ObjectProperty.prop_iSup_iff _ _).mpr
    refine ⟨n + 1 + m, ?_⟩
    rw [S.extensionProductIter_add (show n + 1 = n + 1 from rfl)]
    exact ⟨_, _, _, _, _, hT, hn, hm⟩)
  have : H.IsTriangulated := {}
  have hsmall : ∀ n X, S.extensionProductIter n X → IsAlphaSmall X α := by
    intro n
    induction n with
    | zero => exact fun X hX ↦ hX.isAlphaSmall
    | succ n ih =>
      rw [S.extensionProductIter_succ]
      rintro X ⟨A, B, a, b, c, hT, hA, hB⟩
      exact IsAlphaSmall.extension α _ hT hA.isAlphaSmall (ih B hB)
  have hfactor : ∀ n X, S.extensionProductIter n X → FactorsOut H X := by
    intro n
    induction n with
    | zero =>
      intro X hX I Y f
      obtain ⟨Z, hZ, a, g, hg⟩ := IsAlphaCompact.factorizationClass α X hX I Y f
      exact ⟨Z, fun i ↦ hSH _ (hZ i), a, g, hg⟩
    | succ n ih =>
      rw [S.extensionProductIter_succ]
      rintro X ⟨A, B, a, b, c, hT, hA, hB⟩
      let T := Triangle.mk a b c
      apply factorsOut_cone H T.invRotate (inv_rot_of_distTriang _ hT)
      · exact ih _ ((S.extensionProductIter n).le_shift (-1) _ hB)
      · intro I Y f
        obtain ⟨Z, hZ, a, g, hg⟩ := IsAlphaCompact.factorizationClass α A hA I Y f
        exact ⟨Z, fun i ↦ hSH _ (hZ i), a, g, hg⟩
      · exact ih _ ((S.extensionProductIter n).le_shift 1 _
          ((S.extensionProductIter n).le_shift (-1) _ hB))
  have hHS : H ≤ S := by
    intro X hX
    refine ⟨H, hX, ?_, ?_⟩
    · intro Y hY
      obtain ⟨n, hn⟩ := (ObjectProperty.prop_iSup_iff _ _).mp hY
      exact hsmall n Y hn
    · intro Y hY
      obtain ⟨n, hn⟩ := (ObjectProperty.prop_iSup_iff _ _).mp hY
      exact hfactor n Y hn
  exact hHS _ (H.ext_of_isTriangulatedClosed₂ T hT (hSH _ h₁) (hSH _ h₃))

end CategoryTheory
