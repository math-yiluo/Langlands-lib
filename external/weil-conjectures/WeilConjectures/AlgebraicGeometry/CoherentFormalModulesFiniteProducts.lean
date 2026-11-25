/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesBinaryProducts
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesEmptyProducts

/-! # CoherentFormalModulesFiniteProducts

Source: Stacks Project, Lemma 087X (blueprint: lem-weil-pbc-coherent-formal-finite-products).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Coherent adic inverse systems are closed under ambient finite products.
Source: Stacks Project, Section 087V and Lemma 087X, additive structure of Coh(X,I).
(blueprint: lem-weil-pbc-coherent-formal-finite-products).

Proof: The empty product is the zero system: its terms are coherent, ideal products
are zero, and its reductions are zero. For two coherent systems take their termwise
biproduct. Coherence of each term follows from coherent-kernel-cokernel-locnoeth.
On affine opens, sections of the ideal product of a direct sum are the direct sum
of the ideal products, by ideal-times-quasi-coherent-affine-sections. Thus I^(n+1)
annihilates its level n and quotient by I^(n+1) commutes with the direct sum at
level n+1. The two given quotient isomorphisms give the required quotient
isomorphism of the direct sum, compatibly with its transition. Induction gives
all finite products, since finite products in the ambient preadditive category
are biproducts. The argument applies to any limiting cone by its unique
isomorphism with the termwise product; the three object conditions transport
along that isomorphism. No nonempty index set is assumed.
-/
theorem coherentFormalModules_closedUnderFiniteProducts (X : Scheme.{u})
    [IsNoetherian X] (I : X.IdealSheafData) :
    (IsCoherentFormalModule I).IsClosedUnderFiniteProducts := by
  have hempty : (IsCoherentFormalModule I).IsClosedUnderLimitsOfShape
      (Discrete PEmpty) := coherentFormalModules_closedUnderEmptyProducts X I
  have hbin : (IsCoherentFormalModule I).IsClosedUnderBinaryProducts :=
    coherentFormalModules_closedUnderBinaryProducts X I
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

end AlgebraicGeometry
