/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureGeneration

/-! # Shifted generators detect isomorphisms on their localizing closure

Source: the blueprint, `sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation`,
closed-adjoint uniqueness and final restriction paragraphs; Stacks Project, Derived Categories,
Tags 0145, 0146, 0149, 0FXC and 05QR (blueprint: lem-sf-localizing-hom-test).

The class of generators is an arbitrary object property. The localizing closure is the existing
intersection of replete triangulated subcategories closed under coproducts indexed in the Hom
universe; neither smallness nor compactness of the generator class is required.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

/-- A morphism between objects of the localizing closure of an arbitrary class is invertible
if postcomposition induces bijections on Hom from every integer shift of every generator.

Source: the blueprint, `theorem-f-shriek-finite-coefficients`, closed-adjoint uniqueness and final
restriction paragraphs; Stacks Project, Derived Categories, Tags 0145, 0146, 0149, 0FXC and 05QR
(blueprint: lem-sf-localizing-hom-test).

Proof plan:
1. Complete `α : B ⟶ G` to a distinguished triangle `B ⟶ G ⟶ K ⟶ B[1]`. Every replete
   triangulated coproduct-closed subcategory containing the generators contains `B` and `G`,
   hence `K` by rotation and extension closure. Thus `K` belongs to the localizing closure
   (`def-weil-triangulated-category`, `def-weil-triangulated-subcategory`).
2. For a shifted generator `W = X[n]`, injectivity of postcomposition by `α[1]` follows from
   the hypothesis for `X[n-1]`. If `f : W ⟶ K`, consecutive composites in the triangle give
   `f ≫ δ ≫ α[1] = 0`, so injectivity gives `f ≫ δ = 0`. Hom-exactness gives `f = g ≫ p`;
   surjectivity writes `g = h ≫ α`, and `α ≫ p = 0` gives `f = 0`
   (`lem-weil-pbc-hom-into-triangle-exact`, Stacks 0146 and 0149).
3. Let `Q` be the replete class of all integer shifts of `K`. It is shift-stable, so its
   left orthogonal is replete and triangulated (`lem-sf-shift-stable-left-orthogonal`,
   Stacks 0FXC). It is closed under small coproducts: every map from a coproduct into an
   object of `Q` restricts to zero on each summand, hence is zero by coproduct uniqueness.
   This includes the empty coproduct.
4. Inverse shifts identify maps from a generator to `K[m]` with maps from its `[-m]` shift
   to `K`, so step 2 puts every generator in this left orthogonal. Consequently it contains
   the localizing closure, hence `K`. Since `K` itself is in `Q` up to the shift-zero
   isomorphism, its identity is zero and `K` is a zero object. No coproduct indexed by
   the generator class is used.
5. The zero-cone criterion gives `IsIso α` (`lem-kun-distinguished-cone-zero`, Stacks 05QR).
-/
theorem isIso_of_bijective_postcomp_shift_generators
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [HasCoproducts.{v} C] (S : ObjectProperty C) {B G : C} (α : B ⟶ G)
    (hB : S.localizingClosure B) (hG : S.localizingClosure G)
    (hα : ∀ (X : C), S X → ∀ (n : ℤ),
      Function.Bijective (fun (f : X⟦n⟧ ⟶ B) ↦ f ≫ α)) : IsIso α := by
  let P := S.shiftClosure ℤ
  have hpost : ∀ (X : C), P X →
      Function.Bijective (fun (f : X ⟶ B) ↦ f ≫ α) := by
    rintro X ⟨Y, n, e, hY⟩
    constructor
    · intro f g h
      apply (cancel_epi e.inv).mp
      apply (hα Y hY n).injective
      simpa only [Category.assoc] using congrArg (fun k ↦ e.inv ≫ k) h
    · intro g
      obtain ⟨f, hf⟩ := (hα Y hY n).surjective (e.inv ≫ g)
      refine ⟨e.hom ≫ f, ?_⟩
      dsimp only at hf ⊢
      rw [Category.assoc, hf, e.hom_inv_id_assoc]
  obtain ⟨K, p, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle α
  let T := Pretriangulated.Triangle.mk α p δ
  have hK : S.localizingClosure K :=
    S.localizingClosure.ext_of_isTriangulatedClosed₃ T hT hB hG
  have hvan : ∀ (X : C), P X → ∀ (f : X ⟶ K), f = 0 := by
    intro X hX f
    have hδ : f ≫ δ = 0 := by
      let adj := (shiftEquiv' C (-1 : ℤ) 1 (by simp)).toAdjunction
      let g := (adj.homEquiv X B).symm (f ≫ δ)
      have hg : g ≫ α = 0 := by
        apply (adj.homEquiv X G).injective
        rw [adj.homEquiv_naturality_right]
        simp only [g, Equiv.apply_symm_apply, Adjunction.homEquiv_unit,
          Functor.map_zero, comp_zero]
        change (f ≫ δ) ≫ α⟦(1 : ℤ)⟧' = 0
        have hcomp : δ ≫ α⟦(1 : ℤ)⟧' = 0 :=
          Pretriangulated.comp_distTriang_mor_zero₃₁ T hT
        rw [Category.assoc, hcomp, comp_zero]
      have hg₀ : g = 0 :=
        (hpost _ (P.le_shift (-1 : ℤ) X hX)).injective (by simpa using hg)
      rw [← (adj.homEquiv X B).apply_symm_apply (f ≫ δ)]
      change (adj.homEquiv X B) g = 0
      simp [hg₀, Adjunction.homEquiv_unit]
    obtain ⟨g, hg⟩ := T.coyoneda_exact₃ hT f hδ
    obtain ⟨h, rfl⟩ := (hpost X hX).surjective g
    rw [hg]
    change (h ≫ α) ≫ p = 0
    have hcomp : α ≫ p = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ T hT
    rw [Category.assoc, hcomp, comp_zero]
  have hS : S ≤ (shiftsOf K).leftOrthogonal := by
    rintro X hX W f ⟨n, ⟨e⟩⟩
    let adj := (shiftEquiv' C (-n) n (by simp)).toAdjunction
    have h₀ := hvan (X⟦-n⟧) ⟨X, -n, Iso.refl _, hX⟩
      ((adj.homEquiv X K).symm (f ≫ e.hom))
    rw [← cancel_mono e.hom, zero_comp,
      ← (adj.homEquiv X K).apply_symm_apply (f ≫ e.hom), h₀]
    simp [Adjunction.homEquiv_unit]
  have hzero : IsZero K := by
    rw [IsZero.iff_id_eq_zero]
    exact S.localizingClosure_le hS K hK (𝟙 K)
      ⟨0, ⟨(shiftFunctorZero C ℤ).symm.app K⟩⟩
  exact (T.isZero₃_iff_isIso₁ hT).mp hzero

end CategoryTheory.ObjectProperty
