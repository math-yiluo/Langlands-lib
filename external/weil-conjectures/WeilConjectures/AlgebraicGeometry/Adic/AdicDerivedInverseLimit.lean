/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Adic derived inverse limits with a chosen Roos triangle

Source: literature/blueprint/master/blueprint/sec-proper-base-change/
sk-thm-properbasechange/def-weil-pbc-adic-derived-inverse-limit.md, order 1256;
Stacks Project, Derived Categories, Tags 08TC and 0H9J
(blueprint: def-weil-pbc-adic-derived-inverse-limit).

## Main definitions

- `adicReductionSequence`: the scalar-restricted reductions, indexed from zero.
- `adicReductionStep`: the quotient-induced successive transition maps.
- `adicReductionTower`: the resulting inverse system.
- `AdicDerivedInverseLimit`: an object and chosen maps forming its Roos triangle.

The model parameter uses the recorded coefficient construction. Every derived object
admits such a model by `adicKFlatModel_exists`; no boundedness condition is imposed.
No derived-limit object, morphism between triples, or functor is selected.
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The reductions of K, with scalars restricted to Λ, reindexed by n ↦ n + 1.
The quotient-coefficient version is `adicReduction`; this uses its underlying object.
Source: blueprint order 1256, reduction tower
(blueprint: def-weil-pbc-adic-derived-inverse-limit). -/
noncomputable def adicReductionSequence (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ) : proEtaleDerivedCategory X Λ :=
  adicReductionUnderlying X d M ⟨n + 1, Nat.succ_pos n⟩

end AlgebraicGeometry.Scheme
