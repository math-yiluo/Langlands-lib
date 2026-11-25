/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementIteratePairings
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty

/-! # Tensor pairing of concrete Godement models -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Tensor multiplication for models with the canonical Godement codegeneracies.
Source: Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16; the coordinatewise
construction is applied to sheaves of modules over the structure sheaf.
(blueprint: lem-sc-module-cup-godement-model-pairing-pairing)
Proof: over an open U, send sections s of T(F) and t of T(G) to the family
whose x-coordinate is s(x) tensor t(x), mapped to the stalk of F tensor G.
This is O(U)-bilinear and commutes with restrictions; sheafifying the presheaf
tensor gives a morphism beta(F,G): T(F) tensor T(G) to T(F tensor G).
Its composite with the tensor of the germ units is the germ unit on F tensor G.
Projection to each x and evaluation on stalk representatives prove that beta
commutes with monad multiplication: both composites evaluate the same two
germ representatives at x and then tensor their values. Starting with the
identity pairing on F tensor G, recursively apply beta to the previous
iterates and then apply T to the previous pairing. Induction using these
unit and multiplication identities shows that the degreewise pairings commute
with every unit insertion and multiplication insertion. Transport through the
term equalities in the model predicates. The prescribed codegeneracies are
needed here as well as the prescribed cofaces. Since cofaces and codegeneracies
generate the simplex category, the transported maps form the desired natural
transformation. The three augmentation equations identify their zero components
with the germ units. The unit identity for beta, together with cancellation of
the term and extension isomorphisms, gives the displayed morphism equality.
The tensor of the two single-object identifications is the single-object
identification of F tensor G in degree zero. Empty products and zero module
sheaves satisfy the same coordinate formulas. -/
theorem moduleCup_godement_pairing_for_models (X : Scheme.{u}) (F G : X.Modules)
    (A B C : CosimplicialObject X.Modules)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      (((alternatingCofaceMapComplex X.Modules).obj A).extend
        ComplexShape.embeddingUpNat))
    (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶
      (((alternatingCofaceMapComplex X.Modules).obj B).extend
        ComplexShape.embeddingUpNat))
    (c : (CochainComplex.singleFunctor X.Modules 0).obj (F ⊗ G) ⟶
      (((alternatingCofaceMapComplex X.Modules).obj C).extend
        ComplexShape.embeddingUpNat))
    (hA : ModuleCupGodementModel X F A a)
    (hB : ModuleCupGodementModel X G B b)
    (hC : ModuleCupGodementModel X (F ⊗ G) C c)
    (sA : ModuleCupGodementCodegeneracies X F A)
    (sB : ModuleCupGodementCodegeneracies X G B)
    (sC : ModuleCupGodementCodegeneracies X (F ⊗ G) C) :
    ∃ μ : CategoryTheory.Monoidal.FunctorCategory.tensorObj
        (C := SimplexCategory) (D := X.Modules) A B ⟶ C,
      ((a.f 0) ⊗ₘ (b.f 0)) ≫
        ((((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
          ComplexShape.embeddingUpNat (i := 0) rfl).hom ⊗ₘ
          (((alternatingCofaceMapComplex X.Modules).obj B).extendXIso
          ComplexShape.embeddingUpNat (i := 0) rfl).hom) ≫ μ.app ⦋0⦌ ≫
          (((alternatingCofaceMapComplex X.Modules).obj C).extendXIso
          ComplexShape.embeddingUpNat (i := 0) rfl).inv = c.f 0 := by
  obtain ⟨p, hp0, hpδ, hpσ⟩ := moduleCup_godement_iterate_pairings X F G
  obtain ⟨eA, hAδ, hAa⟩ := hA
  obtain ⟨eB, hBδ, hBb⟩ := hB
  obtain ⟨eC, hCδ, hCc⟩ := hC
  obtain ⟨eA', hAσ⟩ := sA
  obtain ⟨eB', hBσ⟩ := sB
  obtain ⟨eC', hCσ⟩ := sC
  have hσA := (show eA' = eA from Subsingleton.elim _ _) ▸ hAσ
  have hσB := (show eB' = eB from Subsingleton.elim _ _) ▸ hBσ
  have hσC := (show eC' = eC from Subsingleton.elim _ _) ▸ hCσ
  let app : ∀ d : SimplexCategory,
      (CategoryTheory.Monoidal.FunctorCategory.tensorObj A B).obj d ⟶ C.obj d :=
    fun d ↦ (eqToHom (eA d.len) ⊗ₘ eqToHom (eB d.len)) ≫
      p (d.len + 1) ≫ eqToHom (eC d.len).symm
  have hδ (n : ℕ) (i : Fin (n + 2)) :
      (MorphismProperty.naturalityProperty app) (SimplexCategory.δ i) := by
    dsimp [MorphismProperty.naturalityProperty, app,
      CategoryTheory.Monoidal.FunctorCategory.tensorObj]
    apply (cancel_mono (eqToHom (eC (n + 1)))).1
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← hCδ n i]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [tensorHom_comp_tensorHom, ← hAδ n i, ← hBδ n i]
    rw [← tensorHom_comp_tensorHom, Category.assoc, hpδ (n + 1) i]
    simp only [Category.assoc]
  have hσ (n : ℕ) (i : Fin (n + 1)) :
      (MorphismProperty.naturalityProperty app) (SimplexCategory.σ i) := by
    dsimp [MorphismProperty.naturalityProperty, app,
      CategoryTheory.Monoidal.FunctorCategory.tensorObj]
    apply (cancel_mono (eqToHom (eC n))).1
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← hσC n i]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [tensorHom_comp_tensorHom, ← hσA n i, ← hσB n i]
    rw [← tensorHom_comp_tensorHom, Category.assoc, hpσ n i]
    simp only [Category.assoc]
  have hnat := SimplexCategory.morphismProperty_eq_top
    (MorphismProperty.naturalityProperty app) (fun {_} ↦ hδ _) (fun {_} ↦ hσ _)
  let μ : CategoryTheory.Monoidal.FunctorCategory.tensorObj A B ⟶ C :=
    { app := app
      naturality := fun d e f ↦ by
        have h : (MorphismProperty.naturalityProperty app) f := by rw [hnat]; trivial
        exact h }
  refine ⟨μ, ?_⟩
  dsimp [μ, app]
  apply (cancel_mono
    ((((alternatingCofaceMapComplex X.Modules).obj C).extendXIso
      ComplexShape.embeddingUpNat (i := 0) rfl).hom ≫ eqToHom (eC 0))).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [hAa, hBb, hCc]
  rw [← tensorHom_comp_tensorHom_assoc]
  have hu := hpδ 0 (0 : Fin 1)
  simp only [moduleCup_godementInsert, hp0] at hu
  rw [hu]
  simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    eqToIso.hom]
  change (𝟙 F ⊗ₘ 𝟙 G) ≫ 𝟙 (F ⊗ G) ≫ moduleCup_godementUnit X (F ⊗ G) =
    𝟙 (F ⊗ G) ≫ moduleCup_godementUnit X (F ⊗ G)
  simp

end
end AlgebraicGeometry.Scheme.Modules
