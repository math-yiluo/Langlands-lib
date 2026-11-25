/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification

/-! Appending one generic stratum to a complement stratification. -/

@[expose] public section
set_option autoImplicit false
set_option linter.style.longLine false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite reduced stratification whose support is a specified closed subset
(blueprint: lem-a1-finite-etale-noetherian-clopen-assembly-append).

Proof data records the finite partition, its actual scheme immersions, reduced domains,
the property P, and the support and subset equations needed for appending a stratum. -/
structure ReducedFiniteLocallyClosedStratificationOn
    (Y : Scheme.{u})
    (P : (B : Scheme.{u}) → (B ⟶ Y) → Prop)
    (T : TopologicalSpace.Closeds Y) where
  n : ℕ
  stratum : Fin n → Set Y
  isLocallyClosed_stratum : ∀ a, IsLocallyClosed (stratum a)
  pairwise_disjoint_stratum : Pairwise (Function.onFun Disjoint stratum)
  domain : Fin n → Scheme.{u}
  immersion : ∀ a, domain a ⟶ Y
  isImmersion : ∀ a, IsImmersion (immersion a)
  range_immersion : ∀ a, Set.range (immersion a) = stratum a
  isReduced : ∀ a, IsReduced (domain a)
  property : ∀ a, P (domain a) (immersion a)
  support : (⋃ a, stratum a) = (T : Set Y)
  subset : ∀ a, stratum a ⊆ (T : Set Y)

/-- Append an immersed reduced piece to a finite reduced stratification of its closed
complement. This is the finite-index and range bookkeeping step of the induction
(blueprint: lem-a1-finite-etale-noetherian-clopen-assembly-append).

Proof: index by `Fin (n + 1)` via `Fin.cons`: stratum `0` is the range of `j` with domain
`U`, stratum `i + 1` is the old stratum `i` with its domain and arrow unchanged. The range of
the immersion `j` is locally closed; it is disjoint from the old strata, which lie in `T'`;
the union is `range j ∪ T' = T`; reducedness and `P` hold for `U` by hypothesis and for the
old strata by `S`. The support-indexed structure is
needed because an ordinary finite stratification always covers its whole ambient space. -/
theorem append_reduced_stratum_to_complement
    (Y : Scheme.{u})
    (P : (B : Scheme.{u}) → (B ⟶ Y) → Prop)
    (T T' : TopologicalSpace.Closeds Y)
    (U : Scheme.{u}) (j : U ⟶ Y) [IsImmersion j]
    (S : ReducedFiniteLocallyClosedStratificationOn Y P T')
    (hUred : IsReduced U)
    (hdisj : Disjoint (Set.range j) (T' : Set Y))
    (hcover : Set.range j ∪ (T' : Set Y) = (T : Set Y))
    (hP : P U (j)) :
    Nonempty (ReducedFiniteLocallyClosedStratificationOn Y P T) := by
  classical
  let D : Fin (S.n + 1) → Scheme.{u} := Fin.cons U S.domain
  let ι : ∀ a, D a ⟶ Y := Fin.cons (α := fun a => D a ⟶ Y) j S.immersion
  refine ⟨{
    n := S.n + 1
    stratum := Fin.cons (Set.range j) S.stratum
    isLocallyClosed_stratum := by
      intro a
      refine Fin.cases ?_ (fun i => ?_) a
      · exact j.isLocallyClosed_range
      · exact S.isLocallyClosed_stratum i
    pairwise_disjoint_stratum := by
      have h0 : ∀ i, Disjoint (Set.range j) (S.stratum i) := fun i =>
        hdisj.mono_right (S.subset i)
      intro a b hab
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => exact absurd rfl hab
        | succ k => exact h0 k
      | succ i =>
        induction b using Fin.cases with
        | zero => exact (h0 i).symm
        | succ k =>
          exact S.pairwise_disjoint_stratum (fun h => hab (congrArg Fin.succ h))
    domain := D
    immersion := ι
    isImmersion := by
      intro a
      refine Fin.cases ?_ (fun i => ?_) a
      · change IsImmersion j
        infer_instance
      · exact S.isImmersion i
    range_immersion := by
      intro a
      refine Fin.cases ?_ (fun i => ?_) a
      · rfl
      · exact S.range_immersion i
    isReduced := by
      intro a
      refine Fin.cases ?_ (fun i => ?_) a
      · exact hUred
      · exact S.isReduced i
    property := by
      intro a
      refine Fin.cases ?_ (fun i => ?_) a
      · exact hP
      · exact S.property i
    support := by
      rw [← hcover, ← S.support]
      ext y
      simp only [Set.mem_iUnion, Set.mem_union, Fin.exists_fin_succ, Fin.cons_zero,
        Fin.cons_succ]
    subset := by
      intro a
      refine Fin.cases ?_ (fun i => ?_) a
      · rw [← hcover]
        exact Set.subset_union_left
      · refine (S.subset i).trans ?_
        rw [← hcover]
        exact Set.subset_union_right }⟩

end AlgebraicGeometry.Scheme
