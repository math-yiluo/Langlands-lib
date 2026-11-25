/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered

/-! # Hom-colimit criterion for an essentially constant pro-diagram

Source: Stacks Project, Categories, Lemma 05PY (implication (4) => (1))
(blueprint: lem-pur-essential-constant-pro-criterion-05py).
-/

@[expose] public section

universe uJp vJp uCp vCp

open CategoryTheory

namespace CategoryTheory

/-- The Hom-colimit bijections induced by `r` make `G` essentially constant with value `X`.
The cone maps are the preimages of the identity classes, and `r` retracts the leg at `j₀`.

Source: Stacks Project, Categories, Lemma 05PY, implication (4) => (1), dualized;
Lemma 05PZ, implication (4) => (1)
(blueprint: lem-pur-essential-constant-pro-criterion-05py).

Proof (using def-pc-essentially-constant-pro-diagram):
1. For each `j`, bijectivity with `W = G.obj j` gives the unique preimage `u_j` of the
   identity class at `j`. Postcomposition by `G.map a`, for `a : j ⟶ j'`, takes the two
   identity classes to the same class. Injectivity therefore makes the `u_j` natural.
2. Postcompose the defining equality for `u_j₀` by `r`. With `W = X`, both
   `u_j₀ ≫ r` and `𝟙 X` map to the class of `r` at `j₀`; injectivity gives the retraction.
3. The defining equality for `u_j` in the filtered colimit of sets is witnessed at a
   common earlier stage `k`, with maps `a : k ⟶ j₀` and `b : k ⟶ j`. It says
   `G.map b = G.map a ≫ r ≫ u_j`.
4. These natural cone maps, the given `j₀` and `r`, the retraction and the common-stage
   factorization are exactly the witnesses for `IsEssentiallyConstantProDiagram G X`.
   The construction also supplies the asserted identity-class characterization. -/
theorem homColimit_essentiallyConstantProDiagram
    {J : Type uJp} {C : Type uCp} [Category.{vJp} J] [Category.{vCp} C]
    [IsCofiltered J]
    (G : J ⥤ C) (X : C) (j₀ : J) (r : G.obj j₀ ⟶ X)
    (h : ∀ (W : C), Function.Bijective (fun φ : X ⟶ W ↦
      ((G.op ⋙ yoneda.obj W).ιColimitType (Opposite.op j₀) (r ≫ φ)))) :
    IsEssentiallyConstantProDiagram G X ∧
    ∃ (u : (Functor.const J).obj X ⟶ G),
      u.app j₀ ≫ r = 𝟙 X ∧
      (∀ (j : J),
        (G.op ⋙ yoneda.obj (G.obj j)).ιColimitType (Opposite.op j₀)
            (r ≫ u.app j) =
          (G.op ⋙ yoneda.obj (G.obj j)).ιColimitType (Opposite.op j)
            (𝟙 (G.obj j)))
    := by
  classical
  have post {W W' : C} {i j : J} (x : G.obj i ⟶ W) (y : G.obj j ⟶ W)
      (f : W ⟶ W')
      (e : (G.op ⋙ yoneda.obj W).ιColimitType (Opposite.op i) x =
        (G.op ⋙ yoneda.obj W).ιColimitType (Opposite.op j) y) :
      (G.op ⋙ yoneda.obj W').ιColimitType (Opposite.op i) (x ≫ f) =
        (G.op ⋙ yoneda.obj W').ιColimitType (Opposite.op j) (y ≫ f) := by
    obtain ⟨k, a, b, e⟩ :=
      ((G.op ⋙ yoneda.obj W).ιColimitType_eq_iff_of_isFiltered x y).mp e
    apply (G.op ⋙ yoneda.obj W').ιColimitType_eq_of_map_eq_map _ _ a b
    change G.map a.unop ≫ x = G.map b.unop ≫ y at e
    change G.map a.unop ≫ (x ≫ f) = G.map b.unop ≫ (y ≫ f)
    simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ f) e
  choose v hv using fun j ↦ (h (G.obj j)).surjective
    ((G.op ⋙ yoneda.obj (G.obj j)).ιColimitType (Opposite.op j) (𝟙 (G.obj j)))
  let u : (Functor.const J).obj X ⟶ G :=
    { app := v
      naturality := by
        intro i j a
        change 𝟙 X ≫ v j = v i ≫ G.map a
        rw [Category.id_comp]
        symm
        apply (h (G.obj j)).injective
        calc
          _ = (G.op ⋙ yoneda.obj (G.obj j)).ιColimitType
              (Opposite.op i) (G.map a) := by
            simpa using
              post (r ≫ v i) (𝟙 (G.obj i)) (G.map a) (hv i)
          _ = (G.op ⋙ yoneda.obj (G.obj j)).ιColimitType
              (Opposite.op j) (𝟙 (G.obj j)) := by
            simpa using (G.op ⋙ yoneda.obj (G.obj j)).ιColimitType_map
              a.op (𝟙 (G.obj j))
          _ = _ := (hv j).symm }
  have hr : u.app j₀ ≫ r = 𝟙 X := by
    change v j₀ ≫ r = 𝟙 X
    apply (h X).injective
    simpa using
      post (r ≫ v j₀) (𝟙 (G.obj j₀)) r (hv j₀)
  refine ⟨⟨inferInstance, u, j₀, r, hr, ?_⟩, u, hr, hv⟩
  intro j
  obtain ⟨k, a, b, e⟩ :=
    ((G.op ⋙ yoneda.obj (G.obj j)).ιColimitType_eq_iff_of_isFiltered
      (r ≫ v j) (𝟙 (G.obj j))).mp (hv j)
  refine ⟨k.unop, a.unop, b.unop, ?_⟩
  change G.map a.unop ≫ (r ≫ v j) = G.map b.unop ≫ 𝟙 (G.obj j) at e
  simpa only [Category.comp_id] using e.symm

end CategoryTheory
