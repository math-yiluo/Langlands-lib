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
# Universally Japanese rings, Nagata rings, and Japanese schemes

Throughout, "ring" means commutative ring with unit, and "domain" means integral
domain. For a domain `R` we write `K = Frac(R)` for its fraction field. The integral
closure of `R` in a field `L` (with `K ⊆ L`) means the subring
`{x ∈ L | x is integral over R}` of `L`.

These are the algebra and scheme-theoretic notions underlying Stacks Tags 032R, 0BI1,
and 033R (Lemma 28.13.7).

## Definitions

* Definition 1 (N-1, N-2 / Japanese rings — Stacks 0BI0). For a domain `R` with
  fraction field `K`:
  - `R` is N-1 if the integral closure of `R` in `K` is a finite `R`-module.
  - `R` is N-2 (Japanese) if for every finite field extension `L / K` the integral
    closure of `R` in `L` is a finite `R`-module.

* Definition 2 (universally Japanese / Nagata rings — Stacks 032R). For a ring `R`:
  - `R` is universally Japanese if for any finite-type ring map `R → S` with `S` a
    domain, `S` is N-2.
  - `R` is a Nagata ring if `R` is Noetherian and for every prime ideal `p ⊆ R` the
    quotient `R / p` (a domain) is N-2.

* Definition 3 (Japanese scheme — Stacks 033S). An integral scheme `X` is Japanese if
  for every point `x ∈ X` there is an affine open neighbourhood `x ∈ U ⊆ X` whose ring
  `O_X(U)` (a domain, since `X` is integral) is Japanese.

* Definition 4 (Nagata scheme — Stacks 033T). A scheme `X` is Nagata if for every
  point `x ∈ X` there is an affine open neighbourhood `x ∈ U ⊆ X` whose ring `O_X(U)`
  is a Nagata ring.

* Definition 5 (integral closed subscheme). A closed subscheme `Z ⊆ X` is an integral
  closed subscheme if the closed immersion `Z ↪ X` exhibits `Z` as an integral scheme.
  We model such a subscheme by a scheme `Z` together with a closed immersion
  `f : Z ⟶ X` and an `IsIntegral Z` hypothesis (up to isomorphism this is exactly the
  bijective correspondence with irreducible closed subsets given the reduced induced
  structure).

## Main results
* Statement 1 (Stacks Tag 033R, Lemma 28.13.7). Let `X` be a locally Noetherian
  scheme. Then `X` is Nagata if and only if every integral closed subscheme `Z ⊆ X` is
  Japanese.

## Notes

* Finiteness convention: "finite `R`-module" means finitely generated as an `R`-module
  (module-finite), which is `Module.Finite R _`.
* Mathlib does not currently provide the predicates "N-1", "N-2 / Japanese ring",
  "universally Japanese", "Nagata ring", "Japanese scheme", or "Nagata scheme"; these
  are introduced here.
* The integral closure of `R` in an `R`-algebra `A` is `integralClosure R A`, a
  `Subalgebra R A`; here `A` is the relevant field `L`.
* Definitions 3 and 4 are taken in the "exists affine open neighbourhood" form of
  Stacks Definition 28.13.1; by Stacks Lemmas 28.13.4 and 28.13.6 this is equivalent to
  the "for all affine opens" form.
-/

@[expose] public section

open AlgebraicGeometry
open scoped nonZeroDivisors
universe u v

-- Shared helper for both directions.

/-- Module-finiteness of an algebra transfers along a ring isomorphism of the base. -/
private theorem module_finite_of_ringEquiv_algebraMap {K K' L : Type*} [CommRing K] [CommRing K']
    [CommRing L] [Algebra K L] [Algebra K' L] (e : K ≃+* K')
    (h : ∀ k, algebraMap K L k = algebraMap K' L (e k)) (hfin : Module.Finite K' L) :
    Module.Finite K L := by
  rw [← RingHom.finite_algebraMap,
    show algebraMap K L = (algebraMap K' L).comp e.toRingHom from RingHom.ext h]
  exact (RingHom.finite_algebraMap.mpr hfin).comp (RingEquiv.finite e)

/-- **N-2 is invariant under a ring isomorphism, across universes.** -/
lemma IsJapaneseRing.of_ringEquiv {R : Type u} {S : Type v}
    [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] (e : R ≃+* S) (hR : IsJapaneseRing R) : IsJapaneseRing S := by
  refine { finite := fun L _ _ _ _ hfin => ?_ }
  let e' : FractionRing R ≃+* FractionRing S := IsFractionRing.ringEquivOfRingEquiv e
  let _ : Algebra R L := ((algebraMap S L).comp e.toRingHom).toAlgebra
  let _ : Algebra (FractionRing R) L :=
    ((algebraMap (FractionRing S) L).comp e'.toRingHom).toAlgebra
  have hRL : ∀ r : R, (algebraMap R L) r = (algebraMap S L) (e r) := fun _ => rfl
  have hKRL : ∀ k : FractionRing R,
      (algebraMap (FractionRing R) L) k = (algebraMap (FractionRing S) L) (e' k) := fun _ => rfl
  have he' : ∀ r : R, e' (algebraMap R (FractionRing R) r)
      = algebraMap S (FractionRing S) (e r) :=
    fun r => IsFractionRing.ringEquivOfRingEquiv_algebraMap e r
  have htower : IsScalarTower R (FractionRing R) L := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    rw [hRL r, hKRL (algebraMap R (FractionRing R) r), he' r,
      ← IsScalarTower.algebraMap_apply S (FractionRing S) L (e r)]
  have hfinR : Module.Finite (FractionRing R) L := by
    exact module_finite_of_ringEquiv_algebraMap e' hKRL hfin
  exact Module.Finite.integralClosure_of_ringEquiv e rfl
    (module_finite_integralClosure_of_isJapaneseRing hR (FractionRing R) L)

-- Sub-lemmas for the two directions of Statement 1.
