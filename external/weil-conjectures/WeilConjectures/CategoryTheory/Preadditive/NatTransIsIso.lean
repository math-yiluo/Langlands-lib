/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.Preadditive.FinitePowerCokernel
public import WeilConjectures.Mathlib.CategoryTheory.NatIso

/-!
# Components of natural transformations at biproducts and cokernels

Let `τ : F ⟶ G` be a natural transformation of functors between preadditive categories.

- `CategoryTheory.NatTrans.isIso_app_biprod`: if `F` and `G` are additive and `τ` is an
  isomorphism at `X` and at `Y`, then it is an isomorphism at `X ⊞ Y`.
- `CategoryTheory.NatTrans.isIso_app_cokernel`: if `F` and `G` preserve the cokernel of
  `f : X ⟶ Y` and `τ` is an isomorphism at `X` and at `Y`, then it is an isomorphism at
  `cokernel f`.
- `CategoryTheory.NatTrans.isIso_app_cokernel_biproduct_fin`: consequently, if `F` and `G` are
  additive and right exact and `τ` is an isomorphism at `X`, then it is an isomorphism at the
  cokernel of every morphism between finite direct sums of copies of `X`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category C] [Category D]

section Biprod

variable [Preadditive C] [Preadditive D] {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G)

/-- A natural transformation of additive functors which is an isomorphism at `X` and at `Y` is
an isomorphism at `X ⊞ Y`. -/
lemma isIso_app_biprod (X Y : C) [HasBinaryBiproduct X Y] [IsIso (τ.app X)] [IsIso (τ.app Y)] :
    IsIso (τ.app (X ⊞ Y)) := by
  refine ⟨G.map biprod.fst ≫ inv (τ.app X) ≫ F.map biprod.inl +
      G.map biprod.snd ≫ inv (τ.app Y) ≫ F.map biprod.inr, ?_, ?_⟩
  · rw [Preadditive.comp_add, ← τ.naturality_assoc, ← τ.naturality_assoc, IsIso.hom_inv_id_assoc,
      IsIso.hom_inv_id_assoc, ← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id]
  · rw [Preadditive.add_comp, Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      τ.naturality, τ.naturality, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc, ← G.map_comp,
      ← G.map_comp, ← G.map_add, biprod.total, G.map_id]

/-- A natural transformation of additive functors which is an isomorphism at `X` is an
isomorphism at the finite direct sums of copies of `X`. -/
lemma isIso_app_biproduct_fin [HasFiniteBiproducts C] [HasBinaryBiproducts C] (X : C)
    [IsIso (τ.app X)] (n : ℕ) : IsIso (τ.app (⨁ fun _ : Fin n ↦ X)) := by
  induction n with
  | zero =>
    have h := isZero_biproduct_fin_zero fun _ : Fin 0 ↦ X
    exact ⟨0, (F.map_isZero h).eq_of_src _ _, (G.map_isZero h).eq_of_src _ _⟩
  | succ n ih =>
    have := isIso_app_biprod τ X (⨁ fun _ : Fin n ↦ X)
    exact isIso_app_of_iso τ (biproductFinSuccIso fun _ : Fin (n + 1) ↦ X)

end Biprod

section Cokernel

variable [HasZeroMorphisms C] [HasZeroMorphisms D] {F G : C ⥤ D} [F.PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms] (τ : F ⟶ G) {X Y : C} (f : X ⟶ Y) [HasCokernel f]
  [HasCokernel (F.map f)] [HasCokernel (G.map f)]
  [PreservesColimit (parallelPair f 0) F] [PreservesColimit (parallelPair f 0) G]

/-- The component of a natural transformation at a cokernel preserved by both functors is the
map induced on the cokernels. -/
lemma app_cokernel_eq :
    τ.app (cokernel f) = (PreservesCokernel.iso F f).hom ≫
      cokernel.map (F.map f) (G.map f) (τ.app X) (τ.app Y) (τ.naturality f) ≫
        (PreservesCokernel.iso G f).inv := by
  rw [← Iso.inv_comp_eq, Iso.eq_comp_inv]
  refine coequalizer.hom_ext ?_
  rw [cokernel.π_desc, Category.assoc, ← Category.assoc (coequalizer.π _ _),
    (Iso.comp_inv_eq _).2 (PreservesCokernel.π_iso_hom F f).symm, τ.naturality_assoc,
    PreservesCokernel.π_iso_hom]

/-- A natural transformation which is an isomorphism at `X` and at `Y` is an isomorphism at the
cokernel of `f : X ⟶ Y`, if both functors preserve this cokernel. -/
lemma isIso_app_cokernel [IsIso (τ.app X)] [IsIso (τ.app Y)] : IsIso (τ.app (cokernel f)) := by
  rw [app_cokernel_eq τ f]
  have : IsIso (cokernel.map (F.map f) (G.map f) (τ.app X) (τ.app Y) (τ.naturality f)) :=
    (cokernel.mapIso (F.map f) (G.map f) (asIso (τ.app X)) (asIso (τ.app Y))
      (τ.naturality f)).isIso_hom
  infer_instance

end Cokernel

section FinitelyPresented

variable [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C] [HasCokernels C]
  [Preadditive D]
  {F G : C ⥤ D} [F.Additive] [G.Additive] [PreservesFiniteColimits F] [PreservesFiniteColimits G]
  (τ : F ⟶ G)

/-- A natural transformation of right exact additive functors which is an isomorphism at `X` is
an isomorphism at the cokernel of every morphism between finite direct sums of copies of `X`. -/
lemma isIso_app_cokernel_biproduct_fin (X : C) [IsIso (τ.app X)] {m n : ℕ}
    (g : (⨁ fun _ : Fin m ↦ X) ⟶ ⨁ fun _ : Fin n ↦ X) : IsIso (τ.app (cokernel g)) := by
  have := isIso_app_biproduct_fin τ X m
  have := isIso_app_biproduct_fin τ X n
  exact isIso_app_cokernel τ g

end FinitelyPresented

end CategoryTheory.NatTrans
