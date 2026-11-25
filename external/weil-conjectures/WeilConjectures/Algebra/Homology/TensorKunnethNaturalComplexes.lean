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
public import Mathlib.Algebra.DirectSum.Module
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.Algebra.Homology.TensorKunnethNat
import WeilConjectures.Algebra.Homology.TensorTotalExtendNaturalIso

/-! # Tensor Kunneth in natural degrees

Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-tensor-kunneth-natural-complexes).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum
namespace HomologicalComplex

/-- Natural-indexed field tensor Kunneth, with its cocycle representative formula.
Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech; the field tensor
calculation underlying lem-sc-qcoh-cech-total-tensor-nat-iso.
(blueprint: lem-sc-tensor-kunneth-natural-complexes).

Proof: Split each term into boundaries, representatives for homology, and a
complement of cycles. The differential identifies the last complement in degree
p with the boundaries in degree p+1. Tensor the resulting decompositions in the
finite diagonal p+q=n of the natural total. A contractible first factor is
contracted by h tensor 1; a contractible second factor by (-1)^p times 1 tensor h.
The mixed differential terms cancel. The remaining summands are precisely the
tensors of homology representatives. A tensor of cycles is a total cycle by
Leibniz. Changing either cycle by a boundary changes its tensor by a total
boundary, so this pairing descends to homology and is the displayed equivalence.
Its value on each summand is the class of the specified tensor cycle. Degree
zero has one summand; zero complexes give zero groups. There is no boundedness
hypothesis beyond natural indexing, since each total degree has finitely many
summands. Alternatively extend the factors by zero, apply tensor_kunneth_nat,
and use the coprojection-normalized comparison of extension and totalization. -/
theorem tensor_kunneth_natural_complexes {k : Type w} [Field k]
    (A B : CochainComplex (ModuleCat.{w} k) ℕ) (n : ℕ) :
    ∃ e : (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
      (A.homology i.val.1) ⊗[k] (B.homology i.val.2)) ≃ₗ[k]
        (mapBifunctor A B (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ)).homology n,
      ∀ (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
        (a : A.cycles i.val.1) (b : B.cycles i.val.2),
        ∃ z : (mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℕ)).cycles n,
          (mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
              (ComplexShape.up ℕ)).iCycles n z =
            ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ)
              i.val.1 i.val.2 n i.property
              ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 b)) ∧
          e (DirectSum.lof k _ _ i
              ((A.homologyπ i.val.1 a) ⊗ₜ[k] (B.homologyπ i.val.2 b))) =
            (mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
              (ComplexShape.up ℕ)).homologyπ n z  := by
  classical
  let E := ComplexShape.embeddingUpNat
  let T := mapBifunctor A B (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ)
  let S := mapBifunctor (A.extend E) (B.extend E)
    (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)
  obtain ⟨c, hc⟩ := tensorTotal_extend_natural_iso A B
  have hA (p : ℤ) (hp : p < 0) : IsZero ((A.extend E).X p) := by
    apply isZero_extend_X
    intro j hj
    change (j : ℤ) = p at hj
    omega
  have hB (p : ℤ) (hp : p < 0) : IsZero ((B.extend E).X p) := by
    apply isZero_extend_X
    intro j hj
    change (j : ℤ) = p at hj
    omega
  obtain ⟨e, he⟩ := tensor_kunneth_nat (A.extend E) (B.extend E) hA hB n
  let alpha (p : ℕ) := A.extendHomologyIso E (j := p) rfl
  let beta (p : ℕ) := B.extendHomologyIso E (j := p) rfl
  let s := DirectSum.congrLinearEquiv fun i : {pq : ℕ × ℕ // pq.1 + pq.2 = n} ↦
    TensorProduct.congr (alpha i.val.1).symm.toLinearEquiv
      (beta i.val.2).symm.toLinearEquiv
  let t := T.extendHomologyIso E (j := n) rfl
  let d := homologyMapIso c (n : ℤ)
  refine ⟨((s.trans e).trans d.toLinearEquiv).trans t.toLinearEquiv, ?_⟩
  intro i a b
  let aE := (A.extendCyclesIso E (j := i.val.1) rfl).inv a
  let bE := (B.extendCyclesIso E (j := i.val.2) rfl).inv b
  obtain ⟨z, hz, hez⟩ := he i aE bE
  let zE := cyclesMap c.hom (n : ℤ) z
  let zN := (T.extendCyclesIso E (j := n) rfl).hom zE
  have ha : (A.extend E).iCycles (i.val.1 : ℤ) aE =
      (A.extendXIso E (i := i.val.1) rfl).inv (A.iCycles _ a) :=
    congrArg (fun f ↦ f a) (A.extendCyclesIso_inv_iCycles E (j := i.val.1) rfl)
  have hb : (B.extend E).iCycles (i.val.2 : ℤ) bE =
      (B.extendXIso E (i := i.val.2) rfl).inv (B.iCycles _ b) :=
    congrArg (fun f ↦ f b) (B.extendCyclesIso_inv_iCycles E (j := i.val.2) rfl)
  have hzE : (T.extend E).iCycles (n : ℤ) zE =
      (T.extendXIso E (i := n) rfl).inv
        (ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ)
          i.val.1 i.val.2 n i.property ((A.iCycles _ a) ⊗ₜ[k] (B.iCycles _ b))) := by
    have h := congrArg (fun f ↦ f z) (cyclesMap_i c.hom (n : ℤ))
    change (T.extend E).iCycles (n : ℤ) zE = c.hom.f (n : ℤ) (S.iCycles _ z) at h
    rw [h, hz, ha, hb]
    exact hc n i (A.iCycles _ a) (B.iCycles _ b)
  refine ⟨zN, ?_, ?_⟩
  · have h := congrArg (fun f ↦ f zE)
      (T.extendCyclesIso_hom_iCycles E (j := n) rfl)
    change T.iCycles n zN = (T.extendXIso E (i := n) rfl).hom
      ((T.extend E).iCycles (n : ℤ) zE) at h
    rw [h, hzE]
    simp only [Iso.inv_hom_id_apply]
  · have haH : (alpha i.val.1).inv (A.homologyπ _ a) =
        (A.extend E).homologyπ (i.val.1 : ℤ) aE :=
      congrArg (fun f ↦ f a) (A.homologyπ_extendHomologyIso_inv E (j := i.val.1) rfl)
    have hbH : (beta i.val.2).inv (B.homologyπ _ b) =
        (B.extend E).homologyπ (i.val.2 : ℤ) bE :=
      congrArg (fun f ↦ f b) (B.homologyπ_extendHomologyIso_inv E (j := i.val.2) rfl)
    change t.hom (d.hom (e (s (DirectSum.lof k _ _ i
      ((A.homologyπ _ a) ⊗ₜ[k] (B.homologyπ _ b)))))) = _
    simp only [s, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof,
      LinearEquiv.coe_coe, TensorProduct.congr_tmul]
    change t.hom (d.hom (e (DirectSum.lof k _ _ i
      (((alpha i.val.1).inv (A.homologyπ _ a)) ⊗ₜ[k]
        ((beta i.val.2).inv (B.homologyπ _ b)))))) = _
    rw [haH, hbH, hez]
    have h := congrArg (fun f ↦ f z) (homologyπ_naturality c.hom (n : ℤ))
    change d.hom (S.homologyπ _ z) = (T.extend E).homologyπ (n : ℤ) zE at h
    rw [h]
    exact congrArg (fun f ↦ f zE) (T.homologyπ_extendHomologyIso_hom E (j := n) rfl)

end HomologicalComplex
