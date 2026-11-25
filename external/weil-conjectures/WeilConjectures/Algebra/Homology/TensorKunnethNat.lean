/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.DirectSum.Module
import WeilConjectures.Algebra.Homology.TensorKunneth

/-! # Natural-degree indexing of the field-linear tensor Kunneth map

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-qcoh-cech-total-tensor-nat-iso).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum
namespace HomologicalComplex

/-- Reindex the field-linear tensor Kunneth map for complexes supported in nonnegative degrees.
Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech;
the zero extension and reindexing in the proof of lem-sc-picard-kunneth-qcoh-iso-exists.
(blueprint: lem-sc-qcoh-cech-total-tensor-nat-iso).

Proof: Apply tensor_kunneth with lower bounds zero and integer degree n. A complex zero
in negative degrees has zero homology there: its cycles are a subobject of its zero
term, and its homology is a quotient of its cycles. Thus a tensor summand indexed by
(p,q) with p<0 or q<0 is zero. The inclusion of the pairs of nonnegative integers is
therefore an equivalence on direct sums: its inverse projects to those summands and
reindexes by (p.toNat,q.toNat). The two composites are identities on each summand;
on a discarded summand this follows from its being zero. Compose this equivalence
with tensor_kunneth's equivalence. On a natural-degree summand the inclusion changes
only the index; apply the integer-degree cycle formula to get the stated formula.
The equation p+q=n casts to the required integer-degree equation. For n=0 only (0,0)
survives. Zero complexes cause no exception, since their tensor summands are zero. -/
theorem tensor_kunneth_nat {k : Type w} [Field k]
    (A B : CochainComplex (ModuleCat.{w} k) ℤ)
    (hA : ∀ p : ℤ, p < 0 → IsZero (A.X p))
    (hB : ∀ q : ℤ, q < 0 → IsZero (B.X q)) (n : ℕ) :
    ∃ e : (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
      (A.homology (i.val.1 : ℤ)) ⊗[k] (B.homology (i.val.2 : ℤ))) ≃ₗ[k]
        (mapBifunctor A B (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)).homology
          (n : ℤ),
      ∀ (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
        (a : A.cycles (i.val.1 : ℤ)) (b : B.cycles (i.val.2 : ℤ)),
        ∃ z : (mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℤ)).cycles (n : ℤ),
          (mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
              (ComplexShape.up ℤ)).iCycles (n : ℤ) z =
            ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)
              (i.val.1 : ℤ) (i.val.2 : ℤ) (n : ℤ) (by
                change (i.val.1 : ℤ) + (i.val.2 : ℤ) = (n : ℤ)
                exact_mod_cast i.property)
              ((A.iCycles (i.val.1 : ℤ) a) ⊗ₜ[k] (B.iCycles (i.val.2 : ℤ) b)) ∧
          e (DirectSum.lof k _ _ i
              ((A.homologyπ (i.val.1 : ℤ) a) ⊗ₜ[k] (B.homologyπ (i.val.2 : ℤ) b))) =
            (mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
              (ComplexShape.up ℤ)).homologyπ (n : ℤ) z := by
  classical
  let I := {pq : ℕ × ℕ // pq.1 + pq.2 = n}
  let J := {pq : ℤ × ℤ // pq.1 + pq.2 = (n : ℤ)}
  let j : I → J := fun i ↦ ⟨((i.val.1 : ℤ), (i.val.2 : ℤ)), by
    change (i.val.1 : ℤ) + (i.val.2 : ℤ) = (n : ℤ)
    exact_mod_cast i.property⟩
  have hj : Function.Injective j := by
    intro i i' h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    dsimp [j] at h'
    have hp := congrArg Prod.fst h'
    have hq := congrArg Prod.snd h'
    dsimp at hp hq
    exact Prod.ext (Int.ofNat_inj.mp hp) (Int.ofNat_inj.mp hq)
  let M : J → Type w := fun s ↦ (A.homology s.val.1) ⊗[k] (B.homology s.val.2)
  let inc : (⨁ i : I, M (j i)) →ₗ[k] (⨁ s : J, M s) :=
    DirectSum.toModule k I _ (fun i ↦ DirectSum.lof k J M (j i))
  let proj : (⨁ s : J, M s) →ₗ[k] (⨁ i : I, M (j i)) :=
    { toFun := DFinsupp.comapDomain j hj
      map_add' := DFinsupp.comapDomain_add j hj
      map_smul' := DFinsupp.comapDomain_smul j hj }
  have hleft : proj.comp inc = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro i
    ext x i'
    change (DFinsupp.comapDomain j hj
      (inc (DirectSum.lof k I _ i x))) i' = (DirectSum.lof k I (fun i ↦ M (j i)) i x) i'
    simp only [inc, DirectSum.toModule_lof, DFinsupp.comapDomain_apply]
    by_cases h : i = i'
    · subst i'
      simp
    · have h' : j i ≠ j i' := fun hh ↦ h (hj hh)
      simp [DirectSum.lof_eq_of, DirectSum.of_apply, h, h']
  have hinj : Function.Injective inc := by
    intro x y h
    have := congrArg proj h
    simpa only [← LinearMap.comp_apply, hleft, LinearMap.id_apply] using this
  have hsurj : Function.Surjective inc := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero inc⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add inc x' y'⟩
    | of s x =>
      by_cases hp : 0 ≤ s.val.1
      · by_cases hq : 0 ≤ s.val.2
        · let i : I := ⟨(s.val.1.toNat, s.val.2.toNat), by
            have hs := s.property
            dsimp
            omega⟩
          have hi : j i = s := by
            apply Subtype.ext
            dsimp [j, i]
            exact Prod.ext (Int.toNat_of_nonneg hp) (Int.toNat_of_nonneg hq)
          have hs : ∀ (t u : J) (h : t = u) (x : M u),
              ∃ y : M t, DirectSum.lof k J M t y = DirectSum.lof k J M u x := by
            intro t u h x
            subst u
            exact ⟨x, rfl⟩
          obtain ⟨y, hy⟩ := hs (j i) s hi x
          refine ⟨DirectSum.lof k I _ i y, ?_⟩
          change inc (DirectSum.lof k I _ i y) = DirectSum.lof k J M s x
          simpa only [inc, DirectSum.toModule_lof] using hy
        · have hz : IsZero (B.homology s.val.2) :=
            (B.sc s.val.2).isZero_homology_of_isZero_X₂ (hB _ (by omega))
          have : Subsingleton (B.homology s.val.2) :=
            ModuleCat.isZero_iff_subsingleton.mp hz
          have hx : x = 0 := Subsingleton.elim _ _
          exact ⟨0, by simp [hx]⟩
      · have hz : IsZero (A.homology s.val.1) :=
          (A.sc s.val.1).isZero_homology_of_isZero_X₂ (hA _ (by omega))
        have : Subsingleton (A.homology s.val.1) :=
          ModuleCat.isZero_iff_subsingleton.mp hz
        have hx : x = 0 := Subsingleton.elim _ _
        exact ⟨0, by simp [hx]⟩
  obtain ⟨e, he⟩ := tensor_kunneth A B ⟨0, hA⟩ ⟨0, hB⟩ (n : ℤ)
  refine ⟨(LinearEquiv.ofBijective inc ⟨hinj, hsurj⟩).trans e, ?_⟩
  intro i a b
  obtain ⟨z, hz, hez⟩ := he (j i) a b
  refine ⟨z, hz, ?_⟩
  change e (inc (DirectSum.lof k I _ i _)) = _
  rw [show inc (DirectSum.lof k I _ i _) = DirectSum.lof k J M (j i) _ from
    DirectSum.toModule_lof _ _ _]
  exact hez

end HomologicalComplex
