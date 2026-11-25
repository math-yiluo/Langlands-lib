module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Nagata
public import StacksFrontier.RingTheory.Nagata.Shrink
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Checking universal Japaneseness on N-1 finite type domains

This is Stacks project **Tag 0351** (Lemma 10.162.3).

Throughout, all rings are commutative with unit. For a ring map `R → S`, "of finite type"
means `S` is generated as an `R`-algebra by finitely many elements (`Algebra.FiniteType`).
For a domain `R`, write `Frac(R)` (or `K`) for its field of fractions (`IsFractionRing`).
For a ring extension / map `A → B`, the *integral closure of `A` in `B`* is the subring of
`B` consisting of all elements of `B` that are integral over `A` (Mathlib:
`integralClosure A B`). An `R`-module is *finite* if it is finitely generated
(`Module.Finite`).

The relevant definitions are from Stacks Tag 032F (Definition 10.161.1, N-1 / N-2) and
Tag 032R (Definition 10.162.1, universally Japanese).

## Main results
Let `R` be a ring. Suppose:

  (H) For every finite type ring map `R → S` with `S` a domain, the domain `S` is N-1.

Then `R` is universally Japanese.

## Implementation notes

- "Finite type" for a ring map refers to algebra-finiteness, whereas "finite" refers to
  module-finiteness; these are kept distinct (`Algebra.FiniteType` vs `Module.Finite`).
- A fraction field of a domain `R` is encoded as an arbitrary field `K` with
  `[Algebra R K] [IsFractionRing R K]`. Since any two such `K` are canonically isomorphic,
  quantifying over all such `K` faithfully captures "the fraction field".
-/

-- ===== merged from Sec162/Tag0351 =====

@[expose] public section

open AlgebraicGeometry
open scoped nonZeroDivisors
universe u v

/-- The integral closure of `A` in `LL` has `LL` as its field of fractions, provided `LL`
is algebraic over the fraction field `Fr` of `A`. -/
theorem isFractionRing_integralClosure (A : Type*) [CommRing A] [IsDomain A] (Fr : Type*)
    [Field Fr] [Algebra A Fr] [IsFractionRing A Fr] (LL : Type*) [Field LL] [Algebra Fr LL]
    [Algebra A LL] [IsScalarTower A Fr LL] [Algebra.IsAlgebraic Fr LL] :
    IsFractionRing (integralClosure A LL) LL := by
  have : Algebra.IsAlgebraic A Fr := IsLocalization.isAlgebraic Fr (nonZeroDivisors A)
  have : Algebra.IsAlgebraic A LL := Algebra.IsAlgebraic.trans A Fr LL
  have := FaithfulSMul.trans A Fr LL
  exact integralClosure.isFractionRing_of_algebraic fun x hx =>
    FaithfulSMul.algebraMap_injective A LL (by rwa [map_zero])

-- Sub-lemmas for the proof sketch of Stacks Tag 0351.

/-- N-1 for `S` is finiteness of the integral closure of `S` in *any* of its fraction fields: the
canonical isomorphism `Frac S ≃ₐ[S] L` carries one integral closure onto the other. -/
theorem module_finite_integralClosure_of_isN1 (S : Type*) [CommRing S] (L : Type*) [Field L]
    [Algebra S L] [IsFractionRing S L] (h : StacksIsN1 S) : Module.Finite S (integralClosure S L) := by
  let e : FractionRing S ≃ₐ[S] L := IsLocalization.algEquiv (nonZeroDivisors S) _ _
  have he :
    Subalgebra.map (e : FractionRing S →ₐ[S] L) (integralClosure S (FractionRing S)) =
      integralClosure S L :=
    integralClosure_map_algEquiv e
  exact
    Module.Finite.equiv
      (he ▸
          Subalgebra.equivMapOfInjective (integralClosure S (FractionRing S))
            (e : FractionRing S →ₐ[S] L) e.injective).toLinearEquiv
