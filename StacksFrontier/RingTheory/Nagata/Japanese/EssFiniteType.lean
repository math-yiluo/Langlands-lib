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
# Algebras essentially of finite type over a universally Japanese ring

Stacks Tag 032S (Lemma 10.162.4):
If `R` is universally Japanese then any algebra essentially of finite type over
`R` is universally Japanese.

Throughout, all rings are commutative with unit, and "domain" means a commutative
ring that is an integral domain (in particular nonzero).

## Definitions

* (N-1 / N-2 = Japanese, Tag 032F) Let `R` be a domain with field of fractions
  `K = Frac(R)`.
  - `R` is N-1 if the integral closure of `R` in `K` is a finite `R`-module.
  - `R` is N-2 (Japanese) if for every finite field extension `L / K`, the
    integral closure of `R` in `L` is a finite `R`-module.

* (Universally Japanese, Tag 032R) A ring `R` is universally Japanese if for
  every finite type ring map `R → S` with `S` a domain, the ring `S` is N-2.

* (Essentially of finite type, Tag 00QM) A ring map `R → A` is essentially of
  finite type if `A` is isomorphic, as an `R`-algebra, to a localization
  `T⁻¹ B` of an `R`-algebra `B` that is of finite type over `R`. This is already
  available in the environment as `IsEssentiallyOfFiniteType`.

## Conventions

* "Finite module" / "finite over `R`" means finitely generated as an
  `R`-module (`Module.Finite`).
* "Finite type" (for an algebra) means finitely generated as an `R`-algebra
  (`Algebra.FiniteType`).
* A finite field extension `L / K` is encoded as a field `L` which is a
  `K`-algebra with `FiniteDimensional K L`; the `R`-algebra structure on `L`
  factors through `K` via `IsScalarTower R K L`.

## Dependencies

* Tag 0307 ("the integral closure commutes with localization") is available in
  Mathlib as `IsLocalization.integralClosure`.
* Tag 00QM ("essentially of finite type") is available in the environment as
  `IsEssentiallyOfFiniteType`.
-/

-- ===== merged from Sec162/Tag032S =====

@[expose] public section

open AlgebraicGeometry
open scoped nonZeroDivisors
universe u v

-- Auxiliary lemmas (decomposition of the main statement)

/- **Core lemma (the crux: Stacks Tags 032S core / 032G).** If `R` is
universally Japanese and `S` is a *domain* essentially of finite type over `R`,
then `S` is N-2 (Japanese).

This is the heart of Tag 032S. The reduction in the main theorem turns the goal
into exactly this statement (for `S` the given finite-type `A`-algebra domain,
which is essentially of finite type over `R` via the scalar tower).

Argument (Tags 032S and 032G):
Since `S` is essentially of finite type over `R`, write `S = M⁻¹ S₀` where
`S₀ = Algebra.adjoin R s` (a finite generating set `s`) is a *finite-type*
`R`-algebra and `M ⊆ S₀` is a multiplicative set with `S` the localization
`IsLocalization M S`. Because `S` is a domain and `S₀ → S` is a localization,
`S₀` is itself a domain (it embeds into the domain `S`: the localization map is
injective when `M ⊆ nonZeroDivisors`, which holds here since `S` is a domain and
`0 ∉ M`, or one passes to the domain `S₀ / ker`). As a finite-type `R`-algebra
domain, `S₀` is N-2 by `hR` (`R` universally Japanese, Definition 032R).

Now N-2 is preserved under localization of domains (Tag 032G): given a finite
field extension `L / Frac(S)`, note `Frac(S) = Frac(S₀)` (localizations of a
domain share the same fraction field), so `L` is also a finite extension of
`Frac(S₀)`. The integral closure of `S` in `L` equals the localization at `M`
of the integral closure of `S₀` in `L` — this is precisely Tag 0307,
`IsLocalization.integralClosure` (the integral closure commutes with
localization). Since `S₀` is N-2, the integral closure of `S₀` in `L` is a
finite `S₀`-module; localizing, the integral closure of `S` in `L` is a finite
`S`-module. Hence `S` is N-2.

PROOF STRATEGY:
1. From `Algebra.EssFiniteType R S` extract `s` and the localization data; set
   `S₀ := Algebra.adjoin R s`, with `Algebra.FiniteType R S₀` and the
   localization `IsLocalization (Submonoid.comap …) S`.
2. Show `IsDomain S₀` (subalgebra of the domain `S`, or via injectivity of the
   localization map: `IsLocalization.injective` with `M ≤ nonZeroDivisors`).
3. Get `IsN2_032s S₀` from `hR S₀`.
4. Transport N-2 from `S₀` to its localization `S` using
   `IsLocalization.integralClosure` (Tag 0307), matching fraction fields
   (`IsFractionRing`/`FractionRing` of `S` and `S₀` agree) and using that
   localization of a finite module is finite (`IsLocalization`/
   `Module.Finite` base change). This localization-preservation step (Tag 032G)
   is the natural sub-lemma to isolate. -/
/-- **Applying N-2 with an arbitrary fraction field.** If `S₀` is N-2 and `K` is
*any* fraction field of `S₀` (`IsFractionRing S₀ K`), then for every finite
field extension `L / K` the integral closure of `S₀` in `L` is a finite
`S₀`-module.

This generalizes the definition `IsN2_032s S₀` (which is phrased with the specific
fraction field `FractionRing S₀`) to an arbitrary fraction field, by transporting
the data along the canonical algebra isomorphism `FractionRing S₀ ≃ₐ[S₀] K`. -/
lemma isN2_apply_of_isFractionRing (S₀ : Type u) [CommRing S₀] [IsDomain S₀] (h : IsN2_032s S₀)
    (K : Type u) [Field K] [Algebra S₀ K] [IsFractionRing S₀ K] (L : Type u) [Field L]
    [Algebra S₀ L] [Algebra K L] [IsScalarTower S₀ K L] [FiniteDimensional K L] :
    Module.Finite S₀ (integralClosure S₀ L) := by
  let e : FractionRing S₀ ≃ₐ[S₀] K := FractionRing.algEquiv S₀ K
  -- Algebra (FractionRing S₀) K via e
  let : Algebra (FractionRing S₀) K := e.toRingHom.toAlgebra
  have : IsScalarTower S₀ (FractionRing S₀) K := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap S₀ K x = e (algebraMap S₀ (FractionRing S₀) x)
    rw [AlgEquiv.commutes]
  -- give L an Algebra (FractionRing S₀) structure via e then K → L
  let : Algebra (FractionRing S₀) L := ((algebraMap K L).comp e.toRingHom).toAlgebra
  have : IsScalarTower S₀ (FractionRing S₀) L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap S₀ L x = (algebraMap K L) (e (algebraMap S₀ (FractionRing S₀) x))
    rw [AlgEquiv.commutes]
    rw [← IsScalarTower.algebraMap_apply S₀ K L]
  have : IsScalarTower (FractionRing S₀) K L := by
    apply IsScalarTower.of_algebraMap_eq
    intro y
    change (algebraMap K L) (e y) = algebraMap K L (algebraMap (FractionRing S₀) K y)
    rfl
  have : Module.Finite (FractionRing S₀) K := by
    have : Function.Surjective (algebraMap (FractionRing S₀) K) := e.surjective
    exact Module.Finite.of_surjective (Algebra.linearMap (FractionRing S₀) K) this
  have : FiniteDimensional (FractionRing S₀) L := Module.Finite.trans K L
  exact h L
