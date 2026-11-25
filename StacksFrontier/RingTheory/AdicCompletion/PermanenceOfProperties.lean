module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra
public import Mathlib.Algebra.AlgebraicCard
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Expand
public import StacksFrontier.RingTheory.AdicCompletion.Flat.LimitExactness
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension
public import StacksFrontier.RingTheory.Nagata.PthRoot
public import StacksFrontier.RingTheory.AdicCompletion.QuotEquivMapPow
public import StacksFrontier.RingTheory.AnalyticallyUnramified.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksFrontier.RingTheory.Nagata.MonogenicN1
public import StacksFrontier.RingTheory.AdicCompletion.SmulTopPow
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion
public import StacksFrontier.RingTheory.Flat.TowerLTensor
public import StacksFrontier.RingTheory.AdicCompletion.CompletionMap

set_option autoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section
open Stacks.Flatness.NilpotentFibreCriterion

/-!
# Permanence of local properties under adic completion

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

07NV, 07NW, 07NX, 07NY, 0AP1, 07NZ, 0FIZ, 0C23, 0C4G, 0AGX.

## Tag 07NV — Dimension of a completed local ring

The Krull dimension of a Noetherian local ring is unchanged by completion at its maximal ideal.

### Main definitions

No new definitions are introduced.

### Main results

* `ringKrullDim_adicCompletion_maximalIdeal`: completion at the maximal ideal preserves
  the Krull dimension of a Noetherian local ring.

### Implementation notes

The completion is represented by `AdicCompletion (IsLocalRing.maximalIdeal A) A`, Mathlib's
inverse-limit model of the adic completion.

### References

* [The Stacks Project, Tag 07NV](https://stacks.math.columbia.edu/tag/07NV)

## Tag 07NW — Depth of a completed local ring

The depth of a Noetherian local ring is unchanged by completion at its maximal ideal.

### Main definitions

No new definitions are introduced.

### Main results

* `depth_adicCompletion_maximalIdeal`: completion at the maximal ideal preserves the
  depth of a Noetherian local ring.

### Implementation notes

The completion is represented by `AdicCompletion (IsLocalRing.maximalIdeal A) A`, Mathlib's
inverse-limit model of the adic completion. Ring depth is expressed as `Module.depth` of the ring
over itself along its maximal ideal.

### References

* [The Stacks Project, Tag 07NW](https://stacks.math.columbia.edu/tag/07NW)

## Tag 07NX — Cohen–Macaulayness and completion of local rings

A Noetherian local ring is Cohen–Macaulay if and only if its completion at the maximal ideal is
Cohen–Macaulay.

### Main definitions

No new definitions are introduced.

### Main results

* `isMaximalCohenMacaulay_iff_adicCompletion_maximalIdeal`: completion at the maximal
  ideal preserves and reflects Cohen–Macaulayness of a Noetherian local ring.

### Implementation notes

The completion is represented by `AdicCompletion (IsLocalRing.maximalIdeal A) A`, Mathlib's
inverse-limit model of the adic completion. Cohen–Macaulayness of a local ring `A` is expressed as
`Module.IsMaximalCohenMacaulay A A`.

### References

* [The Stacks Project, Tag 07NX](https://stacks.math.columbia.edu/tag/07NX)

## Tag 07NY — Regularity and completion of local rings

A Noetherian local ring is regular if and only if its completion at the maximal ideal is regular.

### Main definitions

No new definitions are introduced.

### Main results

* `isRegularLocalRing_iff_adicCompletion_maximalIdeal`: completion at the maximal ideal
  preserves and reflects regularity of a Noetherian local ring.

### Implementation notes

The completion is represented by `AdicCompletion (IsLocalRing.maximalIdeal A) A`, Mathlib's
inverse-limit model of the adic completion. Regularity is expressed by `IsRegularLocalRing`.

### References

* [The Stacks Project, Tag 07NY](https://stacks.math.columbia.edu/tag/07NY)

## Tag 0AP1 — Discrete valuation rings and completion

A Noetherian local ring is a discrete valuation ring exactly when its completion at the maximal
ideal is a discrete valuation ring.

### Main definitions

No new definitions are introduced.

### Main results

* `isDiscreteValuationRing_iff_adicCompletion_maximalIdeal`: completion at the maximal
  ideal preserves and reflects the property of being a discrete valuation ring.

### Implementation notes

The completion is represented by `AdicCompletion (IsLocalRing.maximalIdeal A) A`. Since Mathlib's
predicate `IsDiscreteValuationRing` takes an `IsDomain` instance, the assertion that an arbitrary
commutative ring is a discrete valuation ring is expressed by existentially bundling that instance.

### References

* [The Stacks Project, Tag 0AP1](https://stacks.math.columbia.edu/tag/0AP1)

## Tag 07NZ — Reducedness and completion of a Noetherian local ring

For a Noetherian local ring, reducedness of the completion implies reducedness of the ring.
The converse fails in general, even for a local domain, but it holds when the ring is Nagata.

### Main definitions

No new definitions are introduced.

### Main results

* `reducedness_and_adicCompletion`: reducedness descends from completion, need not
  ascend to completion in general, and ascends precisely for reduced Nagata local rings.

### Implementation notes

Reducedness of the completion at the maximal ideal is expressed by
`IsAnalyticallyUnramified`. The counterexample is stated in its stronger source form as a
Noetherian local domain with nonreduced completion.

### References

* [Stacks Project, Tag 07NZ](https://stacks.math.columbia.edu/tag/07NZ)

## Tag 0FIZ — Normality from the completion of a local ring

Let `A` be a Noetherian local ring. If the completion of `A` at its maximal ideal is
normal, then `A` is normal.

### Main definitions

There are no new definitions.

### Main results

* `isNormalRing_of_isNormalRing_adicCompletion`: normality descends from the
  maximal-ideal-adic completion of a Noetherian local ring.

### Implementation notes

The completion `A^∧` is represented by
`AdicCompletion (IsLocalRing.maximalIdeal A) A`. Normality is the local definition
`IsNormalRing`, which applies to commutative rings that need not be domains.

### References

* [Stacks Project, Tag 0FIZ](https://stacks.math.columbia.edu/tag/0FIZ)

## Tag 0C23 — Normality of the completion of a local ring

Let `A` be a Noetherian local ring. If `A` is normal and every fibre of the canonical map
from `A` to its completion is normal, then the completion is normal.

### Main definitions

No new definitions are introduced.

### Main results

* `isNormalRing_adicCompletion_maximalIdeal`: the completion of a normal
  Noetherian local ring with normal formal fibres is normal.

### Implementation notes

The completion `A^∧` is represented by `AdicCompletion (IsLocalRing.maximalIdeal A) A`.
The assertion that the formal fibres of `A` are normal is written as normality of every
`Ideal.Fiber` of the canonical algebra map from `A` to this completion.

### References

* [Stacks Project, Tag 0C23]

## Tag 0C4G — Flatness and completion of local rings

A local homomorphism of Noetherian local rings is flat if and only if the induced homomorphism
between their completions at the maximal ideals is flat.

### Main definitions

* `adicCompletionMap` is the homomorphism on adic completions induced by a ring
  homomorphism carrying the ideal of the source into the ideal of the target.

### Main results

* `adicCompletionMap_flat_iff` characterizes flatness of a local homomorphism by
  flatness of its induced map on completions.

### Implementation notes

The induced map is defined from the compatible maps on all quotients by powers of the two ideals.
The theorem is stated for a ring homomorphism directly, so `RingHom.Flat` records flatness using
the algebra structure determined by that homomorphism.

### References

* [Stacks Project, Tag 0C4G](https://stacks.math.columbia.edu/tag/0C4G)

## Tag 0AGX — Completions along a flat local homomorphism

A flat local homomorphism that identifies the maximal ideals and residue fields induces an
isomorphism on completions.

### Main definitions

No new definitions are introduced.

### Main results

* `exists_adicCompletion_ringEquiv_of_flat` gives the isomorphism between the
  completions and records its compatibility with the original homomorphism.

### Implementation notes

The equality of residue fields in the source is expressed by bijectivity of the canonical map on
residue fields. The conclusion includes a ring equivalence commuting with the canonical maps from
the source ring, thereby specifying that it is the equivalence induced by the given homomorphism.
The proof only uses finite generation of the source maximal ideal, so that hypothesis replaces the
source's stronger Noetherian hypotheses.

### References

* [Stacks Project, Tag 0AGX](https://stacks.math.columbia.edu/tag/0AGX)

-/

/-! ### Stacks Tag 07NV -/

section

section

open IsLocalRing

/-- **Stacks 07NV.** A Noetherian local ring and its completion at the maximal ideal have the
same Krull dimension. -/
@[stacks 07NV]
public theorem ringKrullDim_adicCompletion_maximalIdeal {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] :
    ringKrullDim A = ringKrullDim (AdicCompletion (maximalIdeal A) A) := by
  let B := AdicCompletion (maximalIdeal A) A
  have hnoeth : IsNoetherianRing B := by infer_instance
  have hgd : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have hlo : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(maximalIdeal_comap (algebraMap A B)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal A) (maximalIdeal B)
  have hm : maximalIdeal B = (maximalIdeal A).map (algebraMap A B) := by
    dsimp [B]
    exact AdicCompletion.maximalIdeal_eq_map
  have : Nontrivial (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Ideal.Quotient.nontrivial_iff.mpr (hm ▸ (maximalIdeal.isMaximal B).ne_top)
  have hf : (maximalIdeal B).map
      (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) = ⊥ := by
    rw [hm]
    exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by simp)
  have hdim : (maximalIdeal B).height = (maximalIdeal A).height := by
    rw [hf] at h
    simpa using h
  rw [← maximalIdeal_height_eq_ringKrullDim (R := A),
    ← maximalIdeal_height_eq_ringKrullDim (R := B)]
  exact_mod_cast hdim.symm

end

end

/-! ### Stacks Tag 07NW -/

section

section

open Ideal IsLocalRing

end

end

/-! ### Stacks Tag 07NX -/

section

section

end

end

/-! ### Stacks Tag 07NY -/

section

section

/-- **Stacks 07NY.** A Noetherian local ring is regular if and only if its completion at the
maximal ideal is regular. -/
@[stacks 07NY]
public theorem isRegularLocalRing_iff_adicCompletion_maximalIdeal {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] :
    IsRegularLocalRing A ↔
      IsRegularLocalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  rw [isRegularLocalRing_iff, isRegularLocalRing_iff,
    AdicCompletion.spanFinrank_maximalIdeal_eq,
    ← ringKrullDim_adicCompletion_maximalIdeal]

end

end

/-! ### Stacks Tag 0AP1 -/

section

section

/-- **Stacks 0AP1.** A Noetherian local ring is a discrete valuation ring if and only if its
completion at the maximal ideal is a discrete valuation ring. -/
@[stacks 0AP1]
public theorem isDiscreteValuationRing_iff_adicCompletion_maximalIdeal {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] :
    (∃ _ : IsDomain A, IsDiscreteValuationRing A) ↔
      ∃ _ : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A),
        IsDiscreteValuationRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  let B := AdicCompletion (IsLocalRing.maximalIdeal A) A
  calc
    (∃ _ : IsDomain A, IsDiscreteValuationRing A) ↔
        IsRegularLocalRing A ∧ ringKrullDim A = 1 :=
      (isDiscreteValuationRing_tfae A).out 1 3
    _ ↔ IsRegularLocalRing B ∧ ringKrullDim B = 1 := by
      apply and_congr
      · exact isRegularLocalRing_iff_adicCompletion_maximalIdeal
      · rw [ringKrullDim_adicCompletion_maximalIdeal]
    _ ↔ (∃ _ : IsDomain B, IsDiscreteValuationRing B) :=
      (isDiscreteValuationRing_tfae B).out 3 1

end

end

/-! ### Stacks Tag 07NZ -/

section

section

universe u v

end

end

/-! ### Stacks Tag 0FIZ -/

section

section

universe u

end

end

/-! ### Stacks Tag 0C23 -/

section

section

universe u

end

end

/-! ### Stacks Tag 0C4G -/

section

section

@[expose] public section

universe u v

end

end

section

@[expose] public section

open TensorProduct

universe u v w

open AlgebraTensorModule

end

end

end

/-! ### Stacks Tag 0AGX -/

section

section

open CategoryTheory IsLocalRing AdicCompletion

universe u v

end

end

end

@[expose] public section

universe u v

namespace Stacks.AdicCompletion

end Stacks.AdicCompletion

end
