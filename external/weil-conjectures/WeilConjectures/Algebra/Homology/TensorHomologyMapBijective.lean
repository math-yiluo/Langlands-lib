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

import WeilConjectures.Algebra.Homology.TensorHomologyCoordinates
import WeilConjectures.Algebra.Homology.TensorHomologyProductSpan
import WeilConjectures.Algebra.Homology.TensorHomologyPairing

/-!
# Bijectivity of the canonical tensor homology map over a field

Source: Stacks Project, Varieties, Tag 0BED, field-linear Kunneth identification
at `equation-kunneth-on-cech`, with the complement argument of
`lem-sc-qcoh-cech-total-tensor-iso`, steps 1 and 2.
(blueprint: lem-sc-tensor-homology-map-bijective)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory DirectSum
open scoped TensorProduct

namespace HomologicalComplex

/-- Any linear map with the canonical action on tensors of homology classes is bijective.
Source: Stacks Project, Varieties, Tag 0BED, `equation-kunneth-on-cech`;
the field-linear complement argument in steps 1 and 2 of the parent node.
(blueprint: lem-sc-tensor-homology-map-bijective)

Proof: In every degree choose complements Z_A = B_A direct-sum H_A and
A = Z_A direct-sum C_A, and likewise for B. The restriction of d_A from C_A^p
to B_A^(p+1) is an isomorphism: its kernel is C_A^p intersect Z_A^p = 0,
and its image is d_A(A^p) because d_A vanishes on Z_A^p. Consequently A is
the direct sum of its zero-differential H_A subcomplex and a contractible
subcomplex E_A with terms B_A direct-sum C_A. The inverse of this restriction,
extended by zero on C_A, contracts E_A. Make the same decomposition for B.
Distribute the splittings over each tensor term and each total direct sum.
The summands E_A tensor H_B and E_A tensor E_B are contracted by h_A tensor 1:
the mixed terms have coefficients (-1)^(p-1) and (-1)^p, so cancel.
H_A tensor E_B is contracted by (-1)^p times 1 tensor h_B: the mixed terms
have coefficients (-1)^p and (-1)^(p+1), so cancel. Hence only H_A tensor H_B
contributes homology, and its differential is zero. Its degree-n space is the
direct sum over p+q=n of H_A^p tensor H_B^q. The quotient maps identify H_A^p
with H^p(A) and H_B^q with H^q(B). Under these identifications the inclusion
of the surviving summand acts by the representative equation assumed for f.
All homology classes have cycle representatives, pure tensors span each tensor
product, and the direct-sum inclusions span the source. Therefore f equals
this bijective inclusion-induced map, so is injective and surjective.
The argument uses finite-support direct sums and also covers infinite-dimensional
vector spaces, negative degrees, and characteristic two. -/
theorem tensor_homology_map_bijective {k : Type u} [Field k]
    (A B : CochainComplex (ModuleCat.{u} k) ℤ)
    (hA : ∃ m : ℤ, ∀ p : ℤ, p < m → IsZero (A.X p))
    (hB : ∃ m : ℤ, ∀ q : ℤ, q < m → IsZero (B.X q)) (n : ℤ)
    (f : (⨁ s : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
      (A.homology s.1.1) ⊗[k] (B.homology s.1.2)) →ₗ[k]
      (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℤ)).homology n)
    (hf : ∀ (s : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
        (a : A.cycles s.1.1) (b : B.cycles s.1.2)
        (z : (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℤ)).cycles n),
        (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℤ)).iCycles n z =
          ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
            s.1.1 s.1.2 n s.2
            ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b)) →
        f (DirectSum.lof k _ _ s
          ((A.homologyπ s.1.1 a) ⊗ₜ[k] (B.homologyπ s.1.2 b))) =
          (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
            (ComplexShape.up ℤ)).homologyπ n z) :
    Function.Bijective f := by
  classical
  obtain ⟨r, hr⟩ := tensor_homology_coordinates A B n
  have hrf : r.comp f = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro s
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (A.homologyπ s.1.1)).mp
      inferInstance a
    obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective (B.homologyπ s.1.2)).mp
      inferInstance b
    obtain ⟨c, hc⟩ := tensor_homology_pairing A B s.1.1 s.1.2 n s.2
    obtain ⟨z, hz, _⟩ := hc a b
    change r (f (DirectSum.lof k _ _ s
      ((A.homologyπ s.1.1 a) ⊗ₜ[k] (B.homologyπ s.1.2 b)))) = _
    rw [hf s a b z hz, hr s a b z hz]
    rfl
  refine ⟨Function.LeftInverse.injective (fun x ↦ congrArg (fun g ↦ g x) hrf), ?_⟩
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← tensor_homology_product_span A B hA hB n]
  apply Submodule.span_le.mpr
  rintro x ⟨s, a, b, z, hz, rfl⟩
  exact ⟨DirectSum.lof k _ _ s
    ((A.homologyπ s.1.1 a) ⊗ₜ[k] (B.homologyπ s.1.2 b)), hf s a b z hz⟩

end HomologicalComplex
