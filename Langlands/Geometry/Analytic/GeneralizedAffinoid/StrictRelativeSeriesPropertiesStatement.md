# Noetherianity and closed ideals of strict relative unit-radius series

Author: Worker 948. Worker 105 specified the target. It is a missing
statement prerequisite of the binary Laurent gluing proof work, parent task
`a92a4393-05b7-4b21-9144-482d33069790`.

`Langlands.Analytic.PresentedAffinoidAlgebra.StrictRelativeSeriesPropertiesStatement.{u}`
is a proposition-valued definition. It is not a theorem, and it is not used as
an assumption anywhere. It quantifies over the following data:

- every `K : Type u` with `NormedField K`, `IsUltrametricDist K` and
  `CompleteSpace K`;
- a proof of the explicit scalar hypothesis `∃ c : K, 1 < ‖c‖`;
- every `P : PresentedStrictAffinoidAlgebra K`;
- every `m : ℕ`.

Write `A` for `PresentedAffinoidAlgebra.ofStrict K P` and `S` for
`GeneralizedTateAlgebra (PositivePolyradius.unit (Fin m)) A`. The Lean source
writes both out in full. The conclusion is

```lean
IsNoetherianRing S ∧ ∀ I : Ideal S, IsClosed (I : Set S)
```

So `S` is a Noetherian ring and every ideal of `S` is closed. The unapplied
declaration has type `Prop`, with the single universe parameter `u`, and
`lean_check` reports `statement_returns_prop: true`. The module imports the
published `GeneralizedAffinoid.StrictComparison` module and Mathlib's
`Mathlib.RingTheory.Noetherian.Defs`. It changes no published file.

## The actual objects

The base `A = PresentedAffinoidAlgebra.ofStrict K P` is the published
radius-one generalized presentation of the strict presentation `P`. It has
`P.arity` variables, all of radius one, and its ideal is the inverse image of
`P`'s closed ideal under the radius-one coefficient isometry
`GeneralizedTateAlgebra.unitAlgEquiv`. Its carrier is that actual quotient,
with its quotient norm.

`S` is the published generalized Tate algebra with coefficients in `A`: the
actual subalgebra of formal power series in the `m` variables indexed by
`Fin m` with coefficients in `A`, consisting of the series whose coefficients
tend to zero. Every radius is one, so every weight is one. The norm of `S` is
the supremum of the quotient norms in `A` of the coefficients.

`IsNoetherianRing S` is Mathlib's predicate for the commutative ring `S`:
every ideal is finitely generated. `IsClosed` refers to the topology of the
norm of `S`. The conclusion covers every ideal of `S`, including `⊥` and
`⊤`, and not only finitely generated, proper or closed ones.

## Norm and scalar convention

The norm on `K` is the norm of the given `NormedField K` instance. It is
ultrametric by `IsUltrametricDist K`, and `K` is complete for it. The norms of
`A` and `S` are built from this instance.

The hypothesis `∃ c : K, 1 < ‖c‖` says that the norm of `K` is nontrivial.
It is an explicit proposition, not a change of instance. The statement does
not assume `NontriviallyNormedField K`, and it does not replace the given
`NormedField K` structure on which `ofStrict`, the quotient norm of `A` and
the norm of `S` depend. The hypothesis carries the same condition as the
field of Mathlib's `NontriviallyNormedField`. A proof that needs such an
instance must build it from the witness so that it extends the given
`NormedField K` structure. This is a proof obligation, not part of the
statement.

The statement does not claim that the scalar hypothesis is necessary.
Over a trivially normed field it says nothing.

## Edge cases

No proper-ideal, nonzero-base, reducedness, norm-attainment, closedness or
exactness premise is supplied. The following cases are therefore in scope.
They are obligations for a future proof, not facts proved here.

- `m = 0`. Then `S` is the series algebra in no variables, whose elements are
  constant series.
- `P` may present the zero algebra. Then `A` and `S` are zero rings.
- `A` may be nonreduced and may contain nilpotent elements.
- `I` may be any ideal, including `⊥` and `⊤`.

## Provenance: a derived internal transport target

This is not the transcription of a numbered result of a source. It is an
internal target derived from published Library results. It isolates the
closedness obligation that the binary Laurent argument needs for the actual
relative unit-radius series algebras over presented strict bases.

The intended future proof combines the following published results. This
outline is not a proof, and the statement depends on none of them.

- `Langlands.Analytic.StrictTateAlgebra.isNoetherianRing_tate`
  (module `Langlands.Geometry.Analytic.TateNoetherian`) proves that
  `StrictTateAlgebra (Fin n) K` is Noetherian. It assumes only
  `NormedField K`, `IsUltrametricDist K` and `CompleteSpace K`. The same
  module provides the `IsNoetherianRing` instance for every
  `PresentedStrictAffinoidAlgebra K`.
- `GeneralizedTateAlgebra.unitAlgEquiv` identifies the radius-one generalized
  Tate algebra with the strict Tate algebra isometrically, and
  `PresentedAffinoidAlgebra.ofStrict` and `strictAlgEquiv`
  (module `Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictComparison`)
  compare the generalized presentation with `P`.
- `PresentedAffinoidAlgebra.Adjoin.relativeSeriesMap_surjective` and
  `PresentedAffinoidAlgebra.Adjoin.isometry_relativeSeriesMap`
  (module `Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesComparison`)
  show that the relative series algebra over `A` with polyradius `s` is the
  isometric image of the enlarged quotient `Adjoin.algebra K A s ∅`. That
  quotient presents `A.arity + m` variables with the appended polyradius
  `A.polyradius.append s` and the closure of the ideal generated by the old
  relations. Here `A.polyradius.append s` has all radii one but is not
  syntactically `PositivePolyradius.unit (Fin (A.arity + m))`.
- `Langlands.Analytic.isClosed_ideal_of_noetherian_banach`
  (module `Langlands.Geometry.Analytic.ClosedIdealsBanach`) proves that every
  ideal of a complete Noetherian normed commutative algebra over a
  `NontriviallyNormedField` is closed.

Noetherianity would pass from the finite-variable unit Tate algebra to the
enlarged quotient and then, along the surjective comparison, to `S`. The
Banach closed-ideal theorem would then give closedness. It needs a
`NontriviallyNormedField` instance on `K`, which the proof must package from
the explicit witness while keeping the original `NormedField K` structure. It
also needs `CompleteSpace S` and a normed `K`-algebra structure on `S`. The
Library provides instances for both
(`GeneralizedTateAlgebra.instCompleteSpace` and
`GeneralizedTateAlgebra.instNormedAlgebraOfNormedAlgebra`).

## Intended use

`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRelations.ideal` divides
relative series by the closure `(Ideal.span E).closure` of an ordinary
generated ideal, and the binary Laurent quotients of
`GeneralizedAffinoid.BinaryLaurentDiagram` are built this way with one or two
unit-radius variables. Once this statement is proved, for every set `E` of
equations in `S` the ideal `Ideal.span E` is closed, so Mathlib's
`Ideal.closure_eq_of_isClosed` gives `(Ideal.span E).closure = Ideal.span E`.
Every ordinary generated equation ideal in these series algebras then equals
its closure. This file proves neither that implication nor the statement.

## Source context

The source context of the parent work is Piotr Achinger, *Introduction to
non-Archimedean Geometry*, November 22, 2020, printed p.6 and pp.63–65,
especially Proposition 7.1.1 on p.64. It is registered as
`achinger-2020-non-archimedean-geometry-nov22`, SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`. These
pages of the retained original were read directly. Printed and PDF page
numbers agree.

On p.6 Achinger assumes that the non-Archimedean field `K` is complete and
that its absolute value is nontrivial: `|x| ≠ 1` for some `x ≠ 0`. This is
equivalent to `∃ c : K, 1 < ‖c‖`, because `x` or `x⁻¹` then has norm greater
than one. The proof of Proposition 7.1.1 defines `A⟨f⟩ = A⟨X⟩/(X − f)`,
`A⟨f⁻¹⟩ = A⟨Y⟩/(fY − 1)` and `A⟨f, f⁻¹⟩ = A⟨X, Y⟩/(X − f, fY − 1)` with
ordinary generated ideals. The Library quotients use their closures. This
statement isolates the property that makes the two agree for the Library
carriers. It states no Laurent-series, gluing, exactness, or relative/strict
comparison conclusion, and no new claim is attributed to the source.
