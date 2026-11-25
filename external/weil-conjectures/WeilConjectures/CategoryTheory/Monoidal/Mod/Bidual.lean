/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose

/-!
# The biduality morphism of modules

Let `A` be a commutative monoid in a symmetric monoidal Grothendieck abelian category `C`. For
`A`-modules `M` and `N`, the biduality morphism `M ⟶ Hom_A(Hom_A(M, N), N)`, `m ↦ (φ ↦ φ(m))`
(`CategoryTheory.Mod.bidual`), is the transpose of the identity of `Hom_A(M, N)`. It is natural
in `M` (`CategoryTheory.Mod.bidual_naturality`) and in `N`
(`CategoryTheory.Mod.bidual_comp_ihom_map`). For `N ≅ A` it is an isomorphism if `M` is free of
finite rank (`CategoryTheory.Mod.isIso_bidual_of_iso_biproduct`): it is compatible with finite
direct sums, and for `M = A` it is the identification `A ≅ Hom_A(A, A)`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [SymmetricCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

/-- The biduality morphism `M ⟶ Hom_A(Hom_A(M, N), N)`, `m ↦ (φ ↦ φ(m))`: the transpose of the
identity of `Hom_A(M, N)`. -/
noncomputable def bidual (M N : Mod C A) : M ⟶ (ihom ((ihom M).obj N)).obj N :=
  transpose (𝟙 _)

lemma uncurryHom_bidual (M N : Mod C A) :
    uncurryHom (bidual M N) = (β_ M.X ((ihom M).obj N).X).hom ≫ evaluation M N := by
  rw [bidual, uncurryHom_transpose, uncurryHom, Mod.id_hom', id_whiskerRight, Category.id_comp]

/-- The biduality morphism is natural in `M`. -/
lemma bidual_naturality {M M' : Mod C A} (g : M' ⟶ M) (N : Mod C A) :
    g ≫ bidual M N = bidual M' N ≫ (ihomMap ((ihomMap g).app N)).app N := by
  rw [bidual, bidual, ← transpose_comp_ihomMap, ← transpose_comp, Category.id_comp,
    Category.comp_id]

/-- The biduality morphism is natural in `N`. -/
lemma bidual_comp_ihom_map (M : Mod C A) {N N' : Mod C A} (f : N ⟶ N') :
    bidual M N ≫ (ihom ((ihom M).obj N)).map f =
      bidual M N' ≫ (ihomMap ((ihom M).map f)).app N' := by
  refine uncurryHom_injective ?_
  rw [uncurryHom_comp_ihom_map, uncurryHom_comp_ihomMap, uncurryHom_bidual, uncurryHom_bidual,
    BraidedCategory.braiding_naturality_right_assoc, evaluation_naturality, Category.assoc]

/-- The internal hom out of an isomorphism is an isomorphism. -/
lemma isIso_ihomMap_app {M M' : Mod C A} (g : M ⟶ M') [IsIso g] (N : Mod C A) :
    IsIso ((ihomMap g).app N) :=
  inferInstanceAs (IsIso ((ihomMapIso (asIso g)).hom.app N))

/-- The biduality morphism of `M'` is invertible if that of an isomorphic `M` is. -/
lemma isIso_bidual_of_iso {M M' : Mod C A} (e : M ≅ M') (N : Mod C A) [IsIso (bidual M N)] :
    IsIso (bidual M' N) := by
  have := isIso_ihomMap_app e.inv N
  have := isIso_ihomMap_app ((ihomMap e.inv).app N) N
  have h := bidual_naturality e.inv N
  have : IsIso (bidual M' N ≫ (ihomMap ((ihomMap e.inv).app N)).app N) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((ihomMap ((ihomMap e.inv).app N)).app N)

/-- The biduality morphism into `N'` is invertible if that into an isomorphic `N` is. -/
lemma isIso_bidual_of_iso_right (M : Mod C A) {N N' : Mod C A} (e : N ≅ N')
    [IsIso (bidual M N)] : IsIso (bidual M N') := by
  have := isIso_ihomMap_app ((ihom M).map e.hom) N'
  have h := bidual_comp_ihom_map M e.hom
  have : IsIso (bidual M N' ≫ (ihomMap ((ihom M).map e.hom)).app N') := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((ihomMap ((ihom M).map e.hom)).app N')

attribute [local instance] Mod.isGrothendieckAbelian Abelian.hasFiniteBiproducts

/-- The biduality morphism `A ⟶ Hom_A(Hom_A(A, A), A)` is invertible. -/
lemma isIso_bidual_regular : IsIso (bidual (regular A) (regular A)) := by
  have := isIso_ihomMap_app ((ihomRegularIso (A := A)).inv.app (regular A)) (regular A)
  have h : bidual (regular A) (regular A) ≫
      (ihomMap ((ihomRegularIso (A := A)).inv.app (regular A))).app (regular A) =
        (ihomRegularIso (A := A)).inv.app (regular A) := by
    refine uncurryHom_injective ?_
    have hr : uncurryHom ((ihomRegularIso (A := A)).inv.app (regular A)) =
        rightAct (regular A) := by
      rw [uncurryHom, evaluation_regular]
      erw [← comp_whiskerRight_assoc]
      rw [← Mod.comp_hom', Iso.inv_hom_id_app, Mod.id_hom', id_whiskerRight, Category.id_comp]
    calc _ = (β_ A A).hom ≫ uncurryHom ((ihomRegularIso (A := A)).inv.app (regular A)) := by
          rw [uncurryHom_comp_ihomMap, uncurryHom_bidual,
            BraidedCategory.braiding_naturality_right_assoc]
          rfl
      _ = (β_ A A).hom ≫ (β_ A A).hom ≫ μ[A] := by rw [hr]; rfl
      _ = (β_ A A).hom ≫ μ[A] := by rw [SymmetricCategory.symmetry_assoc, IsCommMonObj.mul_comm]
      _ = _ := by rw [hr]; rfl
  have : IsIso (bidual (regular A) (regular A) ≫
      (ihomMap ((ihomRegularIso (A := A)).inv.app (regular A))).app (regular A)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((ihomMap ((ihomRegularIso (A := A)).inv.app (regular A))).app (regular A))

/-- The covariant functoriality `Hom_A(Hom_A(M', N), N) ⟶ Hom_A(Hom_A(M, N), N)` of the bidual
along `g : M' ⟶ M`. -/
noncomputable abbrev bidualMap {M M' : Mod C A} (g : M' ⟶ M) (N : Mod C A) :
    (ihom ((ihom M').obj N)).obj N ⟶ (ihom ((ihom M).obj N)).obj N :=
  (ihomMap ((ihomMap g).app N)).app N

lemma bidualMap_comp {M M' M'' : Mod C A} (g : M'' ⟶ M') (g' : M' ⟶ M) (N : Mod C A) :
    bidualMap (g ≫ g') N = bidualMap g N ≫ bidualMap g' N := by
  rw [bidualMap, bidualMap, bidualMap, ihomMap_comp, NatTrans.comp_app, ihomMap_comp,
    NatTrans.comp_app]

lemma bidualMap_id (M N : Mod C A) : bidualMap (𝟙 M) N = 𝟙 _ := by
  rw [bidualMap, ihomMap_id, NatTrans.id_app, ihomMap_id, NatTrans.id_app]

lemma bidualMap_add {M M' : Mod C A} (g g' : M' ⟶ M) (N : Mod C A) :
    bidualMap (g + g') N = bidualMap g N + bidualMap g' N := by
  rw [bidualMap, bidualMap, bidualMap, ihomMap_add, NatTrans.app_add, ihomMap_add,
    NatTrans.app_add]

lemma bidualMap_sum {M M' : Mod C A} {ι : Type*} (s : Finset ι) (g : ι → (M' ⟶ M))
    (N : Mod C A) : bidualMap (∑ i ∈ s, g i) N = ∑ i ∈ s, bidualMap (g i) N := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := bidualMap_add (0 : M' ⟶ M) 0 N
    rw [add_zero, left_eq_add] at h
    simpa using h
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bidualMap_add, ih]

/-- The biduality morphism of a finite direct sum is invertible if those of the summands are. -/
lemma isIso_bidual_biproduct {n : ℕ} (M : Fin n → Mod C A) (N : Mod C A)
    [∀ i, IsIso (bidual (M i) N)] : IsIso (bidual (⨁ M) N) := by
  refine ⟨∑ i, bidualMap (biproduct.π M i) N ≫ inv (bidual (M i) N) ≫ biproduct.ι M i,
    ?_, ?_⟩
  · simp only [Preadditive.comp_sum]
    simp_rw [← Category.assoc, ← bidual_naturality, Category.assoc, IsIso.hom_inv_id_assoc]
    exact biproduct.total
  · simp only [Preadditive.sum_comp, Category.assoc]
    simp_rw [bidual_naturality, IsIso.inv_hom_id_assoc, ← bidualMap_comp]
    rw [← bidualMap_sum, biproduct.total, bidualMap_id]

/-- **Biduality for free modules of finite rank.** If `M ≅ Aⁿ` and `N ≅ A`, the biduality
morphism `M ⟶ Hom_A(Hom_A(M, N), N)` is invertible. -/
lemma isIso_bidual_of_iso_biproduct {M N : Mod C A} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ regular A) (e' : regular A ≅ N) : IsIso (bidual M N) := by
  have := isIso_bidual_regular (A := A)
  have := isIso_bidual_biproduct (fun _ : Fin n ↦ regular A) (regular A)
  have := isIso_bidual_of_iso e.symm (regular A)
  exact isIso_bidual_of_iso_right M e'

end CategoryTheory.Mod
