# A common complete field realizing compatible affinoid points

Author: Worker 125.

`Langlands.Analytic.PresentedAffinoidAlgebra.PointAmalgamationStatement`
defines an internal derived analytic prerequisite. It states a proposition;
its proof is a separate obligation.

For every universe `u`, let `K : Type u` be a complete ultrametric normed
field, and let `A`, `B`, and `C` be actual `PresentedAffinoidAlgebra K`
objects. Given bounded `K`-algebra maps `i : A → B` and `j : A → C`,
the inputs are points `x : BanachSpectrum B` and `y : BanachSpectrum C`
whose pullbacks to `A` agree:

```text
BanachSpectrum.comap i.toBoundedRingHom x =
  BanachSpectrum.comap j.toBoundedRingHom y.
```

The proposition asserts the existence of a single type `L : Type u` with
`NormedField L`, `IsUltrametricDist L`, `CompleteSpace L`, and
`NormedAlgebra K L` structures, together with bounded `K`-algebra maps
`f : B → L` and `g : C → L`. They must satisfy

```text
f.comp i = g.comp j,
∀ b : B, ‖f b‖ = x b,
∀ c : C, ‖g c‖ = y c.
```

The commuting equation is equality of the actual bounded `K`-algebra
homomorphisms from `A` to `L`: for every `a : A`, the two images
`f (i a)` and `g (j a)` agree. The other two equations say that the norm
on the same field realizes each given multiplicative seminorm on every
element of its algebra. The existential structures on `L` govern both
maps and both norm identities. The field remains in `Type u`, including
when `u = 0`; no universe enlargement is built into the statement.

The imported objects are the Library's actual finite positive-polyradius
Tate quotients by closed ideals, with their quotient norms. The statement
uses the existing `BoundedAlgHom` and `BanachSpectrum.comap`. Arbitrary
positive real radii, trivial valuations, nonreduced quotients, zero
algebras and empty spectra remain in scope. Points are quantified as
inputs, so an empty spectrum gives no pair of input points. There are no
additional strictness, rational-presentation, domain, nonzero,
algebraicity or spectral-injectivity hypotheses.

The provenance is internal and derived: this interface isolates a
common-field realization needed by the proposed argument for the
all-domain spectrum embedding. It is not a direct transcription of a
numbered source theorem. The source motivation for that surrounding
domain problem is Berkovich, *Non-Archimedean analytic spaces* (Trieste
lectures, 2009), Definition 2.2.1 on page 9 and Fact 2.2.3(i) on page 10.
The retained original was read at those pages: registered source
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Those passages motivate the prerequisite without supplying a direct
statement of this amalgamation proposition. This module provides no
proof of amalgamation or of the all-domain spectrum embedding, and
constructs no tensor product.
