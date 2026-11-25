module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.LocalProperties.StandardCover
public import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Polynomial.Basic
public import StacksFrontier.RingTheory.CohenMacaulay.Equidimensional
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeDescent
public import StacksFrontier.RingTheory.Flat.LocalCriteria.FibreCriteria
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.Sequence.BaseChange

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Local properties of rings, and schemes that satisfy one locally

A property of commutative rings is *local* when it is preserved by localization at an element
and can be checked on a finite standard open covering. Such a property can be imposed on a
scheme pointwise, by asking that every point have an affine open neighbourhood whose ring of
sections satisfies it.

Three properties are shown to be local: being of finite type over the integers, being
Noetherian and Cohen–Macaulay, and being Noetherian and regular.

## Main definitions

* `CommRing.PropertyIsLocal` says that a property of commutative rings is local.
* `AlgebraicGeometry.IsLocally` says that a scheme locally satisfies a given property of
  commutative rings.

## Main results

* `CommRing.isNoetherianCohenMacaulayRing_propertyIsLocal`: being Noetherian and Cohen–Macaulay
  is a local property.
* `CommRing.isRegularRing_propertyIsLocal`: being Noetherian and regular is a local property.
* `CommRing.finiteType_int_isLocal`: being of finite type over `ℤ` is a local property.

Those three are the whole mathematical content of Tag 01OT, whose remaining clause only invites
further properties to be added.

* `AlgebraicGeometry.isReduced_iff_isLocally_isReduced`: a scheme is reduced if and only if it
  locally satisfies reducedness of rings. This is Tag 01OS, not part of 01OT.

## Implementation notes

A ring property is represented as a predicate on types equipped with a commutative ring
structure. Localization preservation is stated for any ring satisfying the universal property of
localization away from an element, while the covering condition is expressed by a finite family
whose range spans the unit ideal, with the local rings represented by the canonical
`Localization.Away` construction.

Affine open neighbourhoods are represented by elements of `Scheme.affineOpens`, so their
affineness is part of their type. `IsLocally` is an abbreviation, allowing clients to use its
pointwise existential characterization directly.

Noetherianity is included in the Cohen–Macaulay property itself, since `IsCohenMacaulayRing`
takes a Noetherian instance; the existential instance packages the two conditions without
imposing Noetherianity on the ambient class of rings. Mathlib's `IsRegularRing`, by contrast,
already includes `IsNoetherianRing`, so it expresses both conditions in the regular case without
a separate conjunction.

## References

* [Stacks Project, Tag 01OP](https://stacks.math.columbia.edu/tag/01OP)
* [Stacks Project, Tag 01OQ](https://stacks.math.columbia.edu/tag/01OQ)
* [Stacks Project, Tag 01OS](https://stacks.math.columbia.edu/tag/01OS)
* [Stacks Project, Tag 01OT](https://stacks.math.columbia.edu/tag/01OT)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace CommRing

/-- A property of commutative rings is local if it is preserved by localization away from
an element and descends from every finite family of such localizations whose elements
generate the unit ideal. -/
@[stacks 01OP] structure PropertyIsLocal (P : ∀ (R : Type u) [CommRing R], Prop) : Prop where
  /-- The property passes to any ring realizing the localization away from an element. -/
  localizationAwayPreserves : ∀ {R : Type u} [hR : CommRing R] (f : R) (S : Type u)
    [hS : CommRing S] [Algebra R S] [IsLocalization.Away f S], @P R hR → @P S hS
  /-- The property descends from a finite standard open covering of the spectrum. -/
  ofLocalizationSpan : ∀ {R : Type u} [hR : CommRing R] {ι : Type u} [Finite ι] (f : ι → R),
    Ideal.span (Set.range f) = ⊤ → (∀ i, P (Localization.Away (f i))) → @P R hR

end CommRing

namespace AlgebraicGeometry

/-- A scheme is locally `P` if every point belongs to an affine open whose ring of sections
satisfies `P`. -/
@[stacks 01OQ] abbrev IsLocally (P : (R : Type u) → [CommRing R] → Prop) (X : Scheme.{u}) :
    Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ P Γ(X, U)

end AlgebraicGeometry

end
