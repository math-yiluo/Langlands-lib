# Trivial-scalar rational quotients as denominator localizations

Statement preparation: Worker 574. Target and mathematical design: Worker 146.

`Langlands.Analytic.StrictTestDomain.TrivialScalarRationalLocalizationStatement.{u}`
is a proposition definition, with no proof of its substantive assertion. It
quantifies over every `K : Type u` with `NormedField K`, `IsUltrametricDist K`
and `CompleteSpace K`, every `P : PresentedStrictAffinoidAlgebra K`, the
hypothesis `∀ c : K, ‖c‖ ≤ 1`, and every `d : RationalData K P`.
Its conclusion is `IsLocalization.Away d.denominator d.algebra`.

The `P`-algebra structure in that conclusion is fixed by a local instance:

```lean
letI : Algebra P d.algebra := d.baseMap.toAlgHom.toRingHom.toAlgebra
IsLocalization.Away d.denominator d.algebra
```

Thus the algebra map is exactly the ring homomorphism underlying the existing
bounded structural map `d.baseMap`. The carrier is the existing actual
closed-ideal Tate quotient `d.algebra`. Mathlib's `IsLocalization.Away`
means localization at the powers of the specified denominator, for this
algebra structure. Neither a carrier nor an algebra structure is supplied
as an extra input. The declaration has type `Prop`; its quantified field and
algebras retain the arbitrary coefficient universe `u`.

The proposition permits zero and nonreduced bases, an empty numerator tuple,
and an empty rational locus. There is no injectivity or nonzero-denominator
assumption. The only additional hypothesis beyond the existing rational data
is the displayed scalar norm bound. `d.no_common_zero` remains the existing
input condition; no polynomial comparison, localization property, spectrum
detection result, sheaf property, or descent statement is assumed.

The following mathematical argument checks the intended truth and scope;
these steps are proof obligations for a successor task, not theorems proved
by this module. If `c ≠ 0`, applying the scalar bound to `c` and `c⁻¹`, and
using multiplicativity of the field norm, gives `‖c‖ = 1`. A unit-radius
restricted series therefore has finite support: convergence of its
coefficients to zero leaves only finitely many coefficients with norm at
least `1/2`, and these are all its nonzero coefficients. Consequently the
finite-variable strict Tate algebra is the ordinary polynomial algebra,
with norm zero at zero and one at every nonzero element. Its topology is
discrete, so taking the closure of a relation ideal adds no relations.
The same applies to the enlarged Tate algebra used in the actual rational
quotient. The chosen series lifts and the existing presentation equivalence
then identify that quotient, along its actual base map, with
`P[Y₁, …, Yₘ] / (gYⱼ - fⱼ)`, where `g = d.denominator` and
`fⱼ = d.numerator j`.

The published
`RationalFactorization.generatesUnitIdeal_iff_no_common_zero` supplies unit
ideal generation by `g, f₁, …, fₘ` from `d.no_common_zero`. A finite relation
`1 = ag + ∑ⱼ bⱼfⱼ` becomes
`1 = g(a + ∑ⱼ bⱼYⱼ)` in the polynomial quotient. Hence the image of `g` is
invertible there. Conversely, any ring map out of `P` making `g` invertible
has exactly one extension through these relations, sending `Yⱼ` to
`fⱼ/g`. This is the ordinary localization universal property and motivates
the stated Mathlib predicate. Turning this argument into Lean, including
the actual presentation comparison and Mathlib's localization criteria,
remains the successor proof task.

This reasoning does not require a reduced or nonzero base. For no
numerators, the unit-ideal condition says that `g` is already a unit, and
the quotient has no new variables. If `g` is nilpotent, its being a unit
forces the rational quotient to be zero; localization away from a
nilpotent is likewise zero. Empty loci and zero quotients are therefore
retained. No inference from injectivity or nonemptiness is used.

The original geometric context is Berkovich, *Non-archimedean analytic
spaces*, Trieste lectures (2009), Exercise 2.2.2(ii), printed/PDF p.9:
rational input elements have no common spectrum zero, and the quotient
has relations `gTᵢ - fᵢ`. The proposition here is an internally derived
specialization of the actual unit-radius Tate and rational quotient
definitions to trivial scalar norm, rather than a result explicitly stated
in that exercise. The source is registered as
`berkovich-2009-trieste-analytic-spaces`, retained PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The printed exercise has inconsistent tuple indices and a subscript on
the denominator in its locus formula; the present statement uses the
existing single denominator and `Fin d.arity` numerator tuple.

Achinger, *Introduction to non-Archimedean Geometry*, November 22, 2020,
printed/PDF p.6, explicitly assumes nontrivial valuation. Its convention
does not justify this trivial-valuation specialization; the elementary
finite-support and algebraic argument above provides the provenance.
The source is registered as
`achinger-2020-non-archimedean-geometry-nov22`, retained PDF SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
No source-specific errata note was found in the current Library or project
notes when checked on 2026-10-26.

This module leaves all imported definitions and the whole-spectrum rational
gluing target unchanged. It supplies a focused statement prerequisite for
that work; it proves neither this localization assertion nor any analytic
descent or gluing theorem.
