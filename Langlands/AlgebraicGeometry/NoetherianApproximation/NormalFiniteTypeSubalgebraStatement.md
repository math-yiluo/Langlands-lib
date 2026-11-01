# Normal finitely generated integer subalgebras

`Langlands.AlgebraicGeometry.NoetherianApproximation.NormalFiniteTypeSubalgebraStatement`
is a proposition definition for arbitrary universe `u`. This file states the
proposition; it supplies no proof.

Let `R : Type u` be a commutative domain that is integrally closed in its
fraction field. For every `s : Finset R`, the proposition asks for an actual
`T : Subalgebra ℤ R` with all four properties:

- `T.FG`: finitely many elements generate `T` as a ℤ-algebra;
- `(↑s : Set R) ⊆ T`: every element of the prescribed finite subset belongs to `T`;
- `IsIntegrallyClosed ↥T`: the ring `T` is integrally closed in its own fraction field;
- `IsNoetherianRing ↥T`: the ring `T` is noetherian.

The ℤ-algebra structure on `R` is canonical. A subalgebra inherits its domain
structure from `R`. Thus integral closedness of `T` is normality of a domain,
as in Stacks Definition 10.37.1. Mathlib's `IsIntegrallyClosed` uses
`FractionRing`; the hypothesis `IsDomain R` makes this a fraction field.
There is no characteristic, dimension, valuation-rank or noetherian
hypothesis on `R`. Fields are included. The last property is redundant
mathematically for a finitely generated ℤ-algebra, but is explicit for
subsequent noetherian approximation arguments.

The provenance is a derived consequence of the registered Stacks ingredients,
rather than a verbatim translation of one numbered assertion. Start with
`A = ℤ[s] ⊆ R`. Stacks Propositions 10.162.15–16 make `A` a Nagata domain.
By Definition 10.161.1 its normalization `B` in `Frac A` is finite over `A`.
It is normal by Lemma 10.37.2, applied to the fraction field. The inclusion
`A ⊆ R` embeds `Frac A` into `Frac R`. Each element of `B` is integral over
`R`, since its monic equation over `A` is also one over `R`. Integral
closedness of `R` therefore places `B` inside `R`. Its image is the desired
subalgebra: it contains `s`, is finite type over ℤ, is normal, and is
noetherian. This paragraph explains why the proposition is the intended
consequence; it is not a Lean proof.

The normalization is taken in `Frac A`. The proposition does not assert
that the integral closure of `A` in all of `Frac R` is finite over `A`.
It also does not assert that `Frac T = Frac R`. It gives no descent of
schemes, line bundles, generic sections or morphism properties. Those
geometric steps, and the arbitrary-valuation two-axis extension theorem,
remain separate proof obligations.

The retained original source is
`stacks-normal-finite-type-subalgebras-2026-11-01`, folder fingerprint
`28b191f332990a0874602649e0970a933c9d769a8ce979d1177ea3f3823ab55d`,
an HTML snapshot acquired on 2026-11-01:

- `032E.html`, Definition 10.162.1 and Propositions 10.162.15–16:
  [Nagata rings](https://stacks.math.columbia.edu/tag/032E).
- `032F.html`, Definition 10.161.1:
  [N-1 and N-2 domains](https://stacks.math.columbia.edu/tag/032F).
- `037B.html`, Definition 10.37.1 and Lemma 10.37.2:
  [Normal domains and integral closure](https://stacks.math.columbia.edu/tag/037B).
