/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper

Modified by Worker 288 (2026): package three assertions from Imperial FLT,
commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean:93-100,
170-223 and 225-232, with hypotheses from lines 28-32 and 102, as separately
universally quantified clauses of one Prop definition. Import the published
canonical maps; omit the original proofs and equivalence constructions.
The grouped target is internal organization, not a stronger source theorem.
The upstream license is retained at licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.LinearAlgebra.RestrictedProduct.Tensor
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic

/-!
# Scalar comparison and bijectivity targets for restricted-product tensor maps

This module states, but does not prove, equality of the underlying canonical
maps and their bijectivity under finite presentation and flatness. Each clause
quantifies its own data, retaining the different hypotheses of the source.
-/

universe uR uM uι uN

namespace RestrictedProduct

/-- The scalar comparison and the two bijectivity assertions for the published
canonical tensor maps. The comparison needs no flatness or finite presentation;
the `R`-linear bijectivity clause allows arbitrary modules, while the `M`-linear
clause uses algebras. Each clause allows every index type, submodule family and
filter. This is a proposition-valued target, not a proof of any clause. -/
def TensorRestrictedProductComparison : Prop :=
  (∀ (R : Type uR) (M : Type uM) [CommRing R] [CommRing M] [Algebra R M]
      (ι : Type uι) (N : ι → Type uN) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)]
      (L : ∀ i, Submodule R (N i)) (ℱ : Filter ι),
      ⇑(lTensorLeft R M N ℱ L) = lTensor R M N ℱ L) ∧
  (∀ (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
      [Module.FinitePresentation R M] [Module.Flat R M]
      (ι : Type uι) (N : ι → Type uN) [∀ i, AddCommGroup (N i)]
      [∀ i, Module R (N i)] (L : ∀ i, Submodule R (N i)) (ℱ : Filter ι),
      Function.Bijective (lTensor R M N ℱ L)) ∧
  (∀ (R : Type uR) (M : Type uM) [CommRing R] [CommRing M] [Algebra R M]
      [Module.Flat R M] [Module.FinitePresentation R M]
      (ι : Type uι) (N : ι → Type uN) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)]
      (L : ∀ i, Submodule R (N i)) (ℱ : Filter ι),
      Function.Bijective (lTensorLeft R M N ℱ L))

end RestrictedProduct
