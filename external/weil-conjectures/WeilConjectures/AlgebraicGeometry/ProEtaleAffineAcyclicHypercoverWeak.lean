/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Componentwise lifting for finite coproducts

The section-lifting step used after identifying evaluation on a finite coproduct with the
product of evaluations on its components.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Componentwise surjectivity gives surjectivity on sections when the restriction maps are
bijective. Source: Stacks Project, proetale.tex, Tag 0F4P, disjoint-union paragraph; sites.tex,
Tags 090K, 090L (auxiliary; not a blueprint node).
Proof: choose component preimages using surjectivity, assemble them by the evaluation bijection,
and verify the result by naturality.
-/
theorem weaklyContractible_of_components
    (X : Scheme.{u}) (W : X.ProEt) (U : SimplicialObject (Over W))
    (hcomponents : ∀ n : ℕ, ∃ (I : Type (u + 1)) (V : I → X.ProEt)
      (maps : (i : I) → V i ⟶ (U.obj (op (SimplexCategory.mk n))).left),
      (∀ F : Sheaf (topology X) (Type (u + 1)),
        Function.Bijective (fun s : F.obj.obj (op (U.obj (op (SimplexCategory.mk n))).left) ↦
          fun i ↦ F.obj.map (maps i).op s)) ∧
      (∀ (i : I) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
        Epi f → Function.Surjective (f.hom.app (op (V i))))) :
    ∀ (n : ℕ) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U.obj (op (SimplexCategory.mk n))).left)) := by
  intro n F G f hf s
  obtain ⟨I, V, maps, hbij, hsurj⟩ := hcomponents n
  choose x hx using fun i => hsurj i F G f hf (G.obj.map (maps i).op s)
  obtain ⟨t, ht⟩ := (hbij F).surjective x
  refine ⟨t, ?_⟩
  apply (hbij G).injective
  funext i
  have hn :=
    congrArg (fun q => q t) (f.hom.naturality (maps i).op)
  change G.obj.map (maps i).op (f.hom.app (op (U.obj (op (SimplexCategory.mk n))).left) t) =
    G.obj.map (maps i).op s
  calc
    G.obj.map (maps i).op (f.hom.app (op (U.obj (op (SimplexCategory.mk n))).left) t) =
        f.hom.app (op (V i)) (F.obj.map (maps i).op t) := by
      simp only [CategoryTheory.comp_apply] at hn ⊢
      exact hn.symm
    _ = f.hom.app (op (V i)) (x i) := by
      exact congrArg (fun q => f.hom.app (op (V i)) q) (congrFun ht i)
    _ = G.obj.map (maps i).op s := hx i

end AlgebraicGeometry.Scheme.ProEt
