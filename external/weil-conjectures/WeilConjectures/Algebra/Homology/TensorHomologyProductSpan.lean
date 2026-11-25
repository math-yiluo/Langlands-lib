/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.CategoryTheory.SplitCategoryNullHomotopy

/-!
# Generation of total homology by product classes

Source: Stacks Project, Varieties, Tag 0BED, `equation-kunneth-on-cech`.
(blueprint: lem-sc-tensor-homology-product-span)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace HomologicalComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem cycle_projector {k : Type u} [Field k]
    (K : CochainComplex (ModuleCat.{u} k) ℤ) :
    ∃ (e : K ⟶ K) (r : ∀ p, K.X p ⟶ K.cycles p),
      (∀ p, e.f p = r p ≫ K.iCycles p) ∧ Nonempty (Homotopy e (𝟙 K)) := by
  have (M : ModuleCat.{u} k) : Projective M := by
    have := Module.projective_of_isSemisimpleRing k M
    exact inferInstance
  have (M : ModuleCat.{u} k) : Injective M := by
    have := Module.injective_of_isSemisimpleRing k M
    exact Module.injective_object_of_injective_module k M
  let s (p : ℤ) := Projective.factorThru (𝟙 (K.homology p)) (K.homologyπ p)
  let P (p : ℤ) := Injective.factorThru (K.homologyπ p) (K.iCycles p)
  have hs (p : ℤ) : s p ≫ K.homologyπ p = 𝟙 _ := by simp [s]
  have hP (p : ℤ) : K.iCycles p ≫ P p = K.homologyπ p := by simp [P]
  have hdP (i p : ℤ) : K.d i p ≫ P p = 0 := by
    rw [← K.toCycles_i i p, Category.assoc, hP, K.toCycles_comp_homologyπ]
  let e : K ⟶ K :=
    { f := fun p ↦ P p ≫ s p ≫ K.iCycles p
      comm' := by
        intro i j hij
        simp only [Category.assoc, K.iCycles_d, comp_zero]
        rw [← Category.assoc, ← Category.assoc, hdP, zero_comp, zero_comp] }
  have he (p : ℤ) : homologyMap e p = 𝟙 _ := by
    rw [← cancel_epi (K.homologyπ p), homologyπ_naturality]
    have hc : cyclesMap e p = K.homologyπ p ≫ s p := by
      rw [← cancel_mono (K.iCycles p), cyclesMap_i]
      simp only [e, Category.assoc, reassoc_of% hP]
    rw [hc, Category.assoc, hs, Category.comp_id]
  obtain ⟨h⟩ := CochainComplex.nonempty_nullHomotopy_of_homologyMap_zero
    (e - 𝟙 K) (fun p ↦ by rw [homologyMap_sub, he, homologyMap_id, sub_self])
  exact ⟨e, (fun p ↦ P p ≫ s p), (fun p ↦ rfl), ⟨Homotopy.equivSubZero.symm h⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Product classes span the homology of the total tensor complex over a field.
Source: Stacks Project, Varieties, Tag 0BED, `equation-kunneth-on-cech`,
and the complement and contraction argument of
`lem-sc-qcoh-cech-total-tensor-iso`, steps 1 and 2.
(blueprint: lem-sc-tensor-homology-product-span)

Proof: Choose complements H to boundaries inside cycles and C to cycles inside
each term, for both complexes. The differential identifies C in degree p with
the boundaries in degree p+1. Thus A splits into the zero-differential complex H_A
and a contractible complex E_A, and likewise B. Distribute these decompositions
through tensor products and the finite-support total direct sums. Every summand
with E_A as first factor is contracted by h_A tensor 1; mixed differential terms
cancel because their coefficients are (-1)^(p-1) and (-1)^p. The summand H_A tensor E_B
is contracted by (-1)^p times 1 tensor h_B. Consequently every total cycle is
homologous to an element of the total H_A tensor H_B summand. Such an element
has finite direct-sum support, and each tensor component is a finite sum of pure
tensors. The chosen H_A and H_B elements are cycles, so these pure tensors give
the product classes displayed in the generating set. Thus their linear span
contains every homology class. This also covers zero complexes, negative degrees,
infinite-dimensional terms, and characteristic two. -/
theorem tensor_homology_product_span {k : Type u} [Field k]
    (A B : CochainComplex (ModuleCat.{u} k) ℤ)
    (hA : ∃ m : ℤ, ∀ p : ℤ, p < m → IsZero (A.X p))
    (hB : ∃ m : ℤ, ∀ q : ℤ, q < m → IsZero (B.X q)) (n : ℤ) :
    Submodule.span k {x | ∃ (s : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
        (a : A.cycles s.1.1) (b : B.cycles s.1.2)
        (z : (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℤ)).cycles n),
        (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℤ)).iCycles n z =
          ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
            s.1.1 s.1.2 n s.2
            ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b)) ∧
        x = (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℤ)).homologyπ n z} = ⊤ :=
by
  classical
  obtain ⟨mA, hmA⟩ := hA
  obtain ⟨mB, hmB⟩ := hB
  clear hmA hmB mA mB
  let T := mapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
  obtain ⟨eA, rA, heA, ⟨hA⟩⟩ := cycle_projector A
  obtain ⟨eB, rB, heB, ⟨hB⟩⟩ := cycle_projector B
  let e : T ⟶ T := mapBifunctorMap eA eB (curriedTensor (ModuleCat.{u} k)) (.up ℤ)
  have hId : mapBifunctorMap (𝟙 A) (𝟙 B) (curriedTensor (ModuleCat.{u} k))
      (.up ℤ) = 𝟙 T := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply mapBifunctor.hom_ext
    intro p q hpq
    rw [ι_mapBifunctorMap]
    simp [T]
  have he : homologyMap e n = 𝟙 _ := by
    have h := (mapBifunctorMapHomotopy₁ hA eB (curriedTensor (ModuleCat.{u} k))
      (.up ℤ)).trans
      (mapBifunctorMapHomotopy₂ (𝟙 A) hB (curriedTensor (ModuleCat.{u} k)) (.up ℤ))
    rw [h.homologyMap_eq n, hId, homologyMap_id]
  have hd : e.f n ≫ T.d n (n + 1) = 0 := by
    apply mapBifunctor.hom_ext
    intro p q hpq
    rw [ι_mapBifunctorMap_assoc, heA, heB]
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    have ha : A.d p (p + 1) (A.iCycles p (rA p x)) = 0 :=
      congrArg (fun f ↦ f (rA p x)) (A.iCycles_d p (p + 1))
    have hb : B.d q (q + 1) (B.iCycles q (rB q y)) = 0 :=
      congrArg (fun f ↦ f (rB q y)) (B.iCycles_d q (q + 1))
    rw [mapBifunctor.d_eq]
    simp only [Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
    rw [mapBifunctor.d₁_eq' A B _ _
      (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
      mapBifunctor.d₂_eq' A B _ _ p
        (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl)]
    simp [curriedTensor, ha, hb]
  let t := T.liftCycles (e.f n) (n + 1) ((ComplexShape.up ℤ).next_eq' rfl) hd
  have ht : t ≫ T.iCycles n = e.f n := T.liftCycles_i _ _ _ _
  have ht' : T.iCycles n ≫ t = cyclesMap e n := by
    rw [← cancel_mono (T.iCycles n), Category.assoc, ht, cyclesMap_i]
  let V := Submodule.span k {x | ∃ (s : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
      (a : A.cycles s.1.1) (b : B.cycles s.1.2) (z : T.cycles n),
      T.iCycles n z = ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k))
        (.up ℤ) s.1.1 s.1.2 n s.2
        ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b)) ∧ x = T.homologyπ n z}
  let qV := ModuleCat.ofHom V.mkQ
  have hq : t ≫ T.homologyπ n ≫ qV = 0 := by
    apply mapBifunctor.hom_ext
    intro p q hpq
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    let z := t (ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k))
      (.up ℤ) p q n hpq (x ⊗ₜ[k] y))
    have hz : T.iCycles n z =
        ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (.up ℤ) p q n hpq
          ((A.iCycles p (rA p x)) ⊗ₜ[k] (B.iCycles q (rB q y))) := by
      have hh := congrArg (fun f ↦ f (x ⊗ₜ[k] y))
        (ι_mapBifunctorMap eA eB (curriedTensor (ModuleCat.{u} k)) (.up ℤ) p q n hpq)
      have hh' := congrArg (fun f ↦ f
        (ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (.up ℤ) p q n hpq (x ⊗ₜ[k] y))) ht
      dsimp only [z]
      change T.iCycles n (t _) = e.f n _ at hh'
      rw [hh']
      change e.f n _ = ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k))
        (.up ℤ) p q n hpq ((eA.f p x) ⊗ₜ[k] (eB.f q y)) at hh
      rw [heA, heB] at hh
      simp only [ModuleCat.comp_apply] at hh
      convert hh using 1
    change V.mkQ (T.homologyπ n z) = 0
    apply (Submodule.Quotient.mk_eq_zero V).mpr
    exact Submodule.subset_span ⟨⟨(p, q), hpq⟩, rA p x, rB q y, z, hz, rfl⟩
  apply top_unique
  intro x hx
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (T.homologyπ n)).mp inferInstance x
  have hq' : T.homologyπ n ≫ qV = 0 := by
    rw [← Category.comp_id (T.homologyπ n), ← he, homologyπ_naturality,
      Category.assoc, ← ht', Category.assoc, hq, comp_zero]
  exact (Submodule.Quotient.mk_eq_zero V).mp (congrArg (fun f ↦ f z) hq')

end HomologicalComplex
