# Proof: Noetherianity and closed ideals of strict relative unit-radius series

Authors: Worker 105 wrote the proof draft (shared draft revision 4 of parent
task `a92a4393-05b7-4b21-9144-482d33069790`). Worker 1177 adapted it into this
Library module.

The theorem
`Langlands.Analytic.PresentedAffinoidAlgebra.strict_relative_series_properties`
proves the published proposition
`Langlands.Analytic.PresentedAffinoidAlgebra.StrictRelativeSeriesPropertiesStatement.{u}`
from module
`Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictRelativeSeriesPropertiesStatement`.
The type of the unapplied theorem is exactly that proposition, for the single
universe parameter `u`. It has no parameters or extra hypotheses: the field
`K`, its instances, the scalar witness, `P` and `m` are all quantified inside
the statement and introduced in the proof. This module does not change the
statement's Lean/Markdown pair or anything it imports.

## The target

For every `K : Type u` with `NormedField K`, `IsUltrametricDist K` and
`CompleteSpace K`, every proof of `∃ c : K, 1 < ‖c‖`, every
`P : PresentedStrictAffinoidAlgebra K` and every `m : ℕ`, write
`A = PresentedAffinoidAlgebra.ofStrict K P` and
`S = GeneralizedTateAlgebra (PositivePolyradius.unit (Fin m)) A`. The statement
asserts

```lean
IsNoetherianRing S ∧ ∀ I : Ideal S, IsClosed (I : Set S)
```

The proof keeps the given `NormedField K` instance, the actual quotient carrier
`A` with its quotient norm and the coefficient norm of `S`. It adds no
assumption that an ideal is proper, that `A` is nonzero or reduced, that a norm
is attained, or that some ideal is closed. So the cases `m = 0`, `A = 0` and
nonreduced `A` are covered by the same argument.

## Step 1: the appended polyradius is the unit polyradius

The private lemma `strict_unit_append` proves

```lean
(ofStrict K P).polyradius.append (PositivePolyradius.unit (Fin m)) =
  PositivePolyradius.unit (Fin (P.arity + m))
```

The polyradius of `ofStrict K P` is by definition
`PositivePolyradius.unit (Fin P.arity)`. After unfolding
`PositivePolyradius.append` and `PositivePolyradius.unit`, both sides are
compared coordinatewise. `Fin.addCases` splits an index of
`Fin (P.arity + m)` into one of the first `P.arity` indices or one of the last
`m`, and `simp` shows that both radii are one in each case. The lemma does not
use `CompleteSpace K`. It is an equality of polyradii, needed because the
appended polyradius is not syntactically the unit polyradius.

## Step 2: Noetherianity without the scalar witness

The theorem `strict_relative_series_noetherian K P m` proves
`IsNoetherianRing S`. It uses only `NormedField K`, `IsUltrametricDist K` and
`CompleteSpace K`, not the scalar witness. Put `s = PositivePolyradius.unit (Fin m)`.

1. The scalar generalized Tate algebra
   `GeneralizedTateAlgebra (A.polyradius.append s) K` is Noetherian. Step 1
   rewrites its polyradius to `PositivePolyradius.unit (Fin (P.arity + m))`.
   The published instance from `Langlands.Geometry.Analytic.TateNoetherian`,
   proved by `Langlands.Analytic.StrictTateAlgebra.isNoetherianRing_tate`, says
   that `StrictTateAlgebra (Fin (P.arity + m)) K` is Noetherian. The inverse of
   the radius-one algebra equivalence `GeneralizedTateAlgebra.unitAlgEquiv K`,
   used as a ring equivalence, carries this to the generalized algebra through
   Mathlib's `isNoetherianRing_of_ringEquiv`.
2. The enlarged quotient `PresentedAffinoidAlgebra.Adjoin.algebra K A s ∅` is
   Noetherian. It is the actual closed-relation quotient of the algebra from
   item 1, and its quotient map
   `PresentedAffinoidAlgebra.presentationMap K (Adjoin.algebra K A s ∅)` is
   surjective by the published `presentationMap_surjective`. Mathlib's
   `isNoetherianRing_of_surjective` applies to the underlying ring map.
3. `S` is Noetherian. The published comparison
   `PresentedAffinoidAlgebra.Adjoin.relativeSeriesMap K A s` maps
   `Adjoin.algebra K A s ∅` to `GeneralizedTateAlgebra s A = S`. It is
   surjective by
   `PresentedAffinoidAlgebra.Adjoin.relativeSeriesMap_surjective`
   (module `GeneralizedAffinoid.RelativeSeriesComparison`), and
   `isNoetherianRing_of_surjective` applies again.

The isometry of the comparison is not used in this step; surjectivity suffices.

## Step 3: closed ideals

The theorem `strict_relative_series_closed K hK P m I` proves
`IsClosed (I : Set S)` from the explicit witness `hK : ∃ c : K, 1 < ‖c‖`.

The proof defines a local `NontriviallyNormedField K` instance as the structure
update `{ (inferInstance : NormedField K) with non_trivial := hK }`. It reuses
every field of the given `NormedField K` instance and only adds `non_trivial`,
so its underlying normed field is the given one definitionally. No norm on `K`,
`A` or `S` changes. With this instance, Step 2 and the published
`Langlands.Analytic.isClosed_ideal_of_noetherian_banach`
(module `Langlands.Geometry.Analytic.ClosedIdealsBanach`) apply to `I`. That
theorem needs a normed `K`-algebra structure, completeness and Noetherianity of
`S`. The first two come from published instances that instance search finds.
`GeneralizedTateAlgebra.instNormedAlgebraOfNormedAlgebra` makes relative series
over the normed `K`-algebra `A` a normed `K`-algebra. Completeness comes from
`GeneralizedTateAlgebra.instCompleteSpace` applied to the complete quotient `A`,
which is complete by `PresentedAffinoidAlgebra.instCompleteSpace`. Both
instances are built from the given `NormedField K`, which the local instance
extends definitionally. Noetherianity is Step 2.

## Step 4: the exact target

`strict_relative_series_properties` introduces `K`, its three instances, the
witness `hK`, `P` and `m`, and returns the pair
`⟨strict_relative_series_noetherian K P m, strict_relative_series_closed K hK P m⟩`.

## Checks

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` builds this
module with no errors or warnings. Inspecting the final theorem shows one
universe parameter `u` and the axioms `propext`, `Classical.choice` and
`Quot.sound` only. A separate private check assigns the unapplied constant
`@strict_relative_series_properties.{u}` directly to
`StrictRelativeSeriesPropertiesStatement.{u}`. These are development checks;
acceptance needs the formal exact-target validation and independent review.

## Provenance and scope

This is internal derived mathematics that combines published Library results.
No new theorem is attributed to an external source. The parent work's source
context is Piotr Achinger, *Introduction to non-Archimedean Geometry*
(November 22, 2020), registered as `achinger-2020-non-archimedean-geometry-nov22`.
That source is context for the statement, not a source of this Lean proof.

This module proves only Noetherianity and closedness of every ideal for these
relative series algebras. It proves no annulus normal form, Laurent exact
sequence, quotient comparison or gluing theorem.
