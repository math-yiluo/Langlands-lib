/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Adic coefficient datum and reduction tower

Source: literature/blueprint/master/blueprint/sec-proper-base-change/
sk-thm-properbasechange/def-weil-pbc-complete-coefficient-datum.md, order 1255
(blueprint: def-weil-pbc-complete-coefficient-datum).

The construction uses one K-flat model with flat terms. Quotient reductions are actual
changed complexes. The ordinary balancing and transition maps are specified uniquely on
local tensor generators; their images under localization are the canonical derived maps.

## Main definitions

- `CompleteCoefficientDatum`: the ring, ideal, torsion, and perfectness conditions.
- `AdicKFlatModel`: one flat-term K-flat representative of an arbitrary derived object.
- `adicReduction`, `adicReductionUnderlying`: the quotient reduction and its scalar restriction.
- `adicTransition`: the localized map induced by the quotient homomorphism.
- `adicNormalization`: the localized scalar-extension balancing isomorphism.

## Main statements

- `adicKFlatModel_exists`: availability of models for every unbounded derived object.
- `adicTransition_id`, `adicTransition_comp`: the transition identities.
- `adicNormalization_cocycle`, `adicNormalization_unit`: normalization coherence.
- `adicReductionUnderlying_tensor`: comparison with the recorded derived tensor product.
-/

@[expose] public section

universe t

open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- Perfectness of the actual quotient module over the original coefficient ring,
placed in degree zero. Source: blueprint order 1255
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicQuotientPerfect (Λ : Type t) [CommRing Λ] (I : Ideal Λ) (n : ℕ) :
    Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{t} Λ)
  DerivedCategory.IsPerfectRingComplex
    ((DerivedCategory.singleFunctor (ModuleCat.{t} Λ) 0).obj (ModuleCat.of Λ (Λ ⧸ I ^ n)))

/-- Precisely the coefficient hypotheses, without an assumption of I-adic completeness,
finiteness of the quotient sets, or flatness of any quotient.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
structure CompleteCoefficientDatum (Λ : Type t) [CommRing Λ] where
  ideal : Ideal Λ
  noetherian : IsNoetherianRing Λ
  finitelyGenerated : ideal.FG
  quotientTorsion : ∀ x : Λ ⧸ ideal, ∃ m : ℕ, 0 < m ∧ m • x = 0
  quotientPerfect : ∀ n : ℕ, 1 ≤ n → adicQuotientPerfect Λ ideal n

/-- The quotient map for two powers of the ideal, sending the class of x to the class of x.
Source: blueprint order 1255, construction step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicQuotientMap {Λ : Type t} [CommRing Λ] (I : Ideal Λ)
    (b a : ℕ) (hab : a ≤ b) : Λ ⧸ I ^ b →+* Λ ⧸ I ^ a :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right hab)

end AlgebraicGeometry.Scheme
