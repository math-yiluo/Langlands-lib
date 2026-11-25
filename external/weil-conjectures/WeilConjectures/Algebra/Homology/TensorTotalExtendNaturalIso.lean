/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns

public import Mathlib.Algebra.Homology.Embedding.Extend
import WeilConjectures.Algebra.Homology.TensorTotalExtendNat

/-! # Normalized extension of natural tensor totals

Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech; natural-degree
zero extension in lem-sc-qcoh-cech-total-tensor-nat-iso.
(blueprint: lem-sc-tensor-total-extend-natural-iso).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace HomologicalComplex

/-- Extension by zero commutes with tensor totalization, with the prescribed
value on each natural bidegree summand. No homology assertion occurs here.
Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech;
the zero-extension/reindexing step of lem-sc-qcoh-cech-total-tensor-nat-iso.
(blueprint: lem-sc-tensor-total-extend-natural-iso).

Proof: In degree n>=0 the nonzero integer tensor summands have p,q>=0.
Reindex these by natural pairs p+q=n. On each use the tensor of the two
extendXIso maps followed by the natural total coprojection and the inverse
extendXIso of the natural total. Negative-coordinate summands are zero and
have the unique zero map. For negative total degree every summand is zero.
Define the inverse in nonnegative degrees using the inverse factor extendXIso
maps and the integer coprojections. On every summand the two composites are
identities; on discarded summands both identities are zero. The maps commute
with differentials because extension preserves the factor differentials and
(-1)^p agrees with the integer sign at the image of p. At degree -1 to 0 the
source is zero. This gives c; evaluating its definition on a natural pure tensor
gives the displayed formula. This is a termwise reindexing and uses neither
field Kunneth nor a geometric external cup. Zero complexes and n=0 are included. -/
theorem tensorTotal_extend_natural_iso {k : Type w} [Field k]
    (A B : CochainComplex (ModuleCat.{w} k) ℕ) :
    let E := ComplexShape.embeddingUpNat
    let T := mapBifunctor A B (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ)
    let S := mapBifunctor (A.extend E) (B.extend E)
      (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)
    ∃ c : S ≅ T.extend E,
      ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
        (a : A.X i.val.1) (b : B.X i.val.2),
        c.hom.f (n : ℤ)
          (ιMapBifunctor (A.extend E) (B.extend E) (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℤ) (i.val.1 : ℤ) (i.val.2 : ℤ) (n : ℤ) (by
              change (i.val.1 : ℤ) + (i.val.2 : ℤ) = (n : ℤ)
              exact_mod_cast i.property)
            (((A.extendXIso E (i := i.val.1) rfl).inv a) ⊗ₜ[k]
              ((B.extendXIso E (i := i.val.2) rfl).inv b))) =
          (T.extendXIso E (i := n) rfl).inv
            (ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ)
              i.val.1 i.val.2 n i.property (a ⊗ₜ[k] b)) := by
  classical
  obtain ⟨s, hs⟩ := tensorTotal_extend_nat A B
  refine ⟨s, ?_⟩
  intro n i a b
  rcases i with ⟨⟨p, q⟩, hi⟩
  dsimp only at hi a b ⊢
  subst n
  have h := congrArg (fun f ↦ f
    (((A.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).inv a) ⊗ₜ[k]
      ((B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv b))) (hs p q)
  simp only [ModuleCat.comp_apply] at h
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul,
    ModuleCat.hom_inv_apply, ModuleCat.hom_inv_apply] at h
  have h' := congrArg
    (((mapBifunctor A B (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ)).extendXIso
      ComplexShape.embeddingUpNat (i := p + q) rfl).inv) h
  erw [ModuleCat.inv_hom_apply] at h'
  exact h'

end HomologicalComplex
