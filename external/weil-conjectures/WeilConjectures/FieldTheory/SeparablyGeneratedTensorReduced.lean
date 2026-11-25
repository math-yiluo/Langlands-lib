/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# Tensoring a reduced algebra with a separably generated field extension

Source: Stacks Project, Algebra, Lemma 10.43.6 (Tag 030U), separably generated case
(blueprint: lem-weil-pbc-separably-generated-tensor-reduced).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

-- The algebraic case of Stacks Tag 030U, using finite subalgebras and residue fields.
private theorem isReduced_tensorProduct_of_separable_algebraic
    (k : Type u) (K : Type v) (S : Type w)
    [Field k] [Field K] [CommRing S] [Algebra k K] [Algebra k S]
    [Algebra.IsSeparable k K] [IsReduced S] : IsReduced (K ⊗[k] S) := by
  have : IsReduced (S ⊗[k] K) := by
    refine isReduced_tensorProduct_of_forall_residueField fun p ↦ ?_
    refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB ↦ ?_
    let : Field B := (B.isField_of_algebraic).toField
    have : Algebra.IsSeparable k B := Algebra.IsSeparable.of_algHom k K B.val
    have : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).mp hB
    have : Algebra.FormallyUnramified k B := Algebra.FormallyUnramified.of_isSeparable k B
    exact Algebra.FormallyUnramified.isReduced_of_field p.asIdeal.ResidueField _
  exact isReduced_of_injective (Algebra.TensorProduct.comm k K S) (AlgEquiv.injective _)

/-- Tensoring a reduced commutative `k`-algebra with a separably generated field extension
of `k` gives a reduced ring. Source: Stacks Project, Algebra, Lemma 10.43.6 (Tag 030U),
separably generated case (blueprint: lem-weil-pbc-separably-generated-tensor-reduced).

Proof:
1. Put `E = k(s)` for the given separating transcendence basis. For each residue field
   of `S`, the source library's
   `isReduced_tensorProduct_adjoin_of_algebraicIndependent` proves reducedness after
   tensoring with `E`, by identifying it with a localization of a polynomial ring.
   `isReduced_tensorProduct_of_forall_residueField` gives reducedness of `S ⊗[k] E`.
2. A separable algebraic extension preserves reducedness: reduce the reduced algebra
   to its residue fields, and the extension to its finitely generated subalgebras using
   `IsReduced.tensorProduct_of_flat_of_forall_fg`. Each such subalgebra is a field,
   separable and of finite type, hence formally unramified. After base change to a
   residue field it is reduced by `Algebra.FormallyUnramified.isReduced_of_field`.
   This argument is proved in the private helper above.
3. Apply step 2 to `K/E` and the reduced `E`-algebra `E ⊗[k] S`. The tensor
   base-change equivalence identifies the result with `K ⊗[k] S`. Reducedness
   transports through this equivalence. -/
theorem isReduced_tensorProduct_of_isSeparablyGenerated
    (k : Type u) (K : Type v) (S : Type w)
    [Field k] [Field K] [CommRing S] [Algebra k K] [Algebra k S] [IsReduced S]
    (hK : IsSeparablyGenerated k K) : IsReduced (K ⊗[k] S) := by
  obtain ⟨s, hs, hsep⟩ := hK
  let E := IntermediateField.adjoin k s
  have : Algebra.IsSeparable E K := hsep
  have hE : IsReduced (S ⊗[k] E) := by
    refine isReduced_tensorProduct_of_forall_residueField fun p ↦ ?_
    have h := isReduced_tensorProduct_adjoin_of_algebraicIndependent
      (K := p.asIdeal.ResidueField) hs.1
    rw [Subtype.range_coe_subtype] at h
    exact h
  have : IsReduced (E ⊗[k] S) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k E S) (AlgEquiv.injective _)
  have : IsReduced (K ⊗[E] (E ⊗[k] S)) :=
    isReduced_tensorProduct_of_separable_algebraic E K (E ⊗[k] S)
  exact isReduced_of_injective
    (Algebra.TensorProduct.cancelBaseChange k E K K S).symm (AlgEquiv.injective _)

end Algebra

