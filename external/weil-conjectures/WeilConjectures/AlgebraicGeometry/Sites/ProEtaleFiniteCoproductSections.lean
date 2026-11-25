/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Evaluation of sheaves on finite coproducts in the pro-etale site

This is the sheaf-theoretic core used by
`WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation`.

## References

* Stacks Project, Tag 0F4P, and Tag 0DB1

## Implementation details

The site-cover argument is kept separate from the geometric construction so that it can be
proved independently.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The empty covering forces a sheaf to have exactly one section on an empty object. -/
private theorem sections_unique_of_isEmpty {X : Scheme.{u}} (T : X.ProEt)
    [IsEmpty T.left] (F : Sheaf (topology X) (Type (max (u + 1) w))) :
    Nonempty (Unique (F.obj.obj (op T))) := by
  exact ⟨Types.isTerminalEquivUnique _ (F.isTerminalOfBotCover T (bot_mem_topology T))⟩

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- Sections on a finite disjoint union are the product of the sections on its summands
(including the empty family). -/
theorem finite_coproduct_sheaf_core (X : Scheme.{u}) (I : Type v) [Finite I]
    (V : I → X.ProEt) (W : X.ProEt) (ι : ∀ i, V i ⟶ W)
    (e : (∐ fun i ↦ (V i).left) ≅ W.left)
    (hqc : ∀ i, CompactSpace (V i).left)
    (hqs : ∀ i, QuasiSeparatedSpace (V i).left)
    (hι : ∀ i, Sigma.ι (fun i ↦ (V i).left) i ≫ e.hom = (ι i).left) :
    (∀ F : Sheaf (topology X) (Type (max (u + 1) w)),
        Function.Bijective (fun s : F.obj.obj (op W) ↦
          fun i ↦ F.obj.map (ι i).op s)) ∧
      (IsEmpty I → IsEmpty W.left ∧
        ∀ F : Sheaf (topology X) (Type (max (u + 1) w)),
          Nonempty (Unique (F.obj.obj (op W)))) := by
  classical
  clear hqc hqs
  have hopen (i : I) : IsOpenImmersion (ι i).left := by
    rw [← hι i]
    infer_instance
  have hcover : ∀ x : W.left, ∃ i y, (ι i).left y = x := by
    intro x
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover (fun i ↦ (V i).left)).exists_eq (e.inv x)
    change (Sigma.ι (fun i ↦ (V i).left) i) y = e.inv x at hy
    refine ⟨i, y, ?_⟩
    rw [← hι i, Hom.comp_apply, hy]
    simp [← Hom.comp_apply]
  have hmem : Presieve.ofArrows V ι ∈ precoverage X W := by
    change (Presieve.ofArrows V ι).map (ProEt.forget X ⋙ Over.forget X) ∈
      proetalePrecoverage W.left
    rw [Presieve.map_ofArrows]
    apply zariskiPrecoverage_le_propQCPrecoverage
    exact (Scheme.Cover.mkOfCovers I (fun i ↦ (V i).left)
      (fun i ↦ (ι i).left) hcover).mem₀
  have hsieve : Sieve.ofArrows V ι ∈ topology X W :=
    Precoverage.generate_mem_toGrothendieck hmem
  have hbij (F : Sheaf (topology X) (Type (max (u + 1) w))) :
      Function.Bijective (fun s : F.obj.obj (op W) ↦
        fun i ↦ F.obj.map (ι i).op s) := by
    have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
    have hglue := (Presieve.isSheafFor_arrows_iff F.obj ι).mp
      (hF.isSheafFor _ hsieve)
    have hcompat (s : ∀ i, F.obj.obj (op (V i))) :
        Presieve.Arrows.Compatible F.obj ι s := by
      intro i j T a b hab
      by_cases hij : i = j
      · subst j
        have hab' : a.left = b.left := by
          apply (cancel_mono (ι i).left).mp
          exact congrArg (fun f ↦ f.left) hab
        have : a = b := MorphismProperty.Over.Hom.ext hab'
        subst b
        rfl
      · have hempty : IsEmpty T.left := by
          apply isEmpty_of_commSq_sigmaι_of_ne
            (g := fun i ↦ (V i).left) (a := a.left) (b := b.left) _ hij
          constructor
          apply (cancel_mono e.hom).mp
          rw [Category.assoc, Category.assoc, hι, hι]
          exact congrArg (fun f ↦ f.left) hab
        obtain ⟨hunique⟩ := sections_unique_of_isEmpty T F
        exact hunique.uniq _ |>.trans (hunique.uniq _).symm
    constructor
    · intro s t hst
      exact (hglue _ (hcompat _)).unique (fun i ↦ rfl) (fun i ↦ congrFun hst.symm i)
    · intro s
      obtain ⟨t, ht, _⟩ := hglue s (hcompat s)
      exact ⟨t, funext ht⟩
  constructor
  · exact hbij
  · intro hI
    let _ : IsEmpty I := hI
    have hempty : IsEmpty W.left := ⟨fun x ↦ by
      obtain ⟨i, _, _⟩ := hcover x
      exact isEmptyElim i⟩
    exact ⟨hempty, fun F ↦ sections_unique_of_isEmpty W F⟩

end AlgebraicGeometry.Scheme.ProEt
