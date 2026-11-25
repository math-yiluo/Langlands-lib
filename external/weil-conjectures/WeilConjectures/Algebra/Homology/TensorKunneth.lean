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
import WeilConjectures.Algebra.Homology.TensorHomologyPairing
import WeilConjectures.Algebra.Homology.TensorHomologyMapBijective

/-!
# The field-linear Kunneth isomorphism

Source: Stacks Project, Varieties, Tag 0BED, `lemma-kunneth`, the tensor-total Cech
step `equation-kunneth-on-cech` (blueprint: lem-sc-qcoh-cech-total-tensor-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory DirectSum
open scoped TensorProduct

namespace HomologicalComplex

/-- Source: Stacks Project, Varieties, Tag 0BED, `lemma-kunneth`, the field-linear
identification in `equation-kunneth-on-cech`
(blueprint: lem-sc-qcoh-cech-total-tensor-iso).

For bounded-below cochain complexes over a field, the direct sum of the tensor products
of their cohomologies is the cohomology of their total tensor complex. The equation on
cycle representatives specifies the canonical map, including its well-definedness:
`iCycles` includes a cocycle, and `homologyπ` takes its cohomology class. The total tensor
complex `mapBifunctor A B (curriedTensor _) (ComplexShape.up ℤ)` (as recorded on
def-pc-tensor-complex-sheaves) uses the differential `d_A ⊗ 1 + (-1)^p 1 ⊗ d_B`.

Proof (the three elementary steps of the node):
1. In every degree choose complements `Z_A = B_A ⊕ H_A` and `A = Z_A ⊕ C_A`, and
similarly for `B`. The differential identifies `C_A^p` with `B_A^(p+1)`. Thus each
complex splits into its cohomology with zero differential and contractible two-term
pieces; the inverse of the differential on each two-term piece is a contracting homotopy.
2. Distribute these splittings through the total tensor direct sums. A tensor summand
with a contractible first factor is contracted by `h_A ⊗ 1`; a summand with a contractible
second factor is contracted by `(-1)^p 1 ⊗ h_B`. In both cases the mixed differential
terms have opposite signs and cancel. Only `H_A ⊗ H_B`, with zero differential, survives.
3. A tensor of cocycles is a cocycle. Replacing either representative by a boundary
changes the tensor by a boundary, by the signed Leibniz differential. Hence the class
map is well defined and bilinear. On the surviving summand it is exactly its inclusion,
so it is an isomorphism in every integer degree. -/
theorem tensor_kunneth {k : Type u} [Field k]
    (A B : CochainComplex (ModuleCat.{u} k) ℤ)
    (hA : ∃ m : ℤ, ∀ p : ℤ, p < m → IsZero (A.X p))
    (hB : ∃ m : ℤ, ∀ q : ℤ, q < m → IsZero (B.X q)) (n : ℤ) :
    ∃ e : (⨁ s : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
      (A.homology s.1.1) ⊗[k] (B.homology s.1.2)) ≃ₗ[k]
      (mapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)).homology n,
      ∀ (s : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
        (a : A.cycles s.1.1) (b : B.cycles s.1.2),
        ∃ z : (mapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)).cycles n,
          (mapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)).iCycles n z =
            ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
              s.1.1 s.1.2 n s.2
              ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b)) ∧
          e (DirectSum.lof k _ _ s
            ((A.homologyπ s.1.1 a) ⊗ₜ[k] (B.homologyπ s.1.2 b))) =
              (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
                (ComplexShape.up ℤ)).homologyπ n z :=
  by
  classical
  let T := mapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
  let S := {pq : ℤ × ℤ // pq.1 + pq.2 = n}
  choose c hc using fun s : S ↦ tensor_homology_pairing A B s.1.1 s.1.2 n s.2
  let f : (⨁ s : S, (A.homology s.1.1) ⊗[k] (B.homology s.1.2)) →ₗ[k]
      T.homology n := DirectSum.toModule k S _ (fun s ↦ TensorProduct.lift (c s))
  have hf : ∀ (s : S) (a : A.cycles s.1.1) (b : B.cycles s.1.2)
      (z : T.cycles n),
      T.iCycles n z =
        ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
          s.1.1 s.1.2 n s.2 ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b)) →
      f (DirectSum.lof k _ _ s
        ((A.homologyπ s.1.1 a) ⊗ₜ[k] (B.homologyπ s.1.2 b))) = T.homologyπ n z := by
    intro s a b z hz
    obtain ⟨z', hz', hc'⟩ := hc s a b
    have hzz : z' = z := by
      apply (ModuleCat.mono_iff_injective (T.iCycles n)).mp inferInstance
      exact hz'.trans hz.symm
    subst z'
    simpa only [f, DirectSum.toModule_lof, TensorProduct.lift.tmul] using hc'
  refine ⟨LinearEquiv.ofBijective f
    (tensor_homology_map_bijective A B hA hB n f hf), ?_⟩
  intro s a b
  obtain ⟨z, hz, _⟩ := hc s a b
  exact ⟨z, hz, hf s a b z hz⟩

end HomologicalComplex
