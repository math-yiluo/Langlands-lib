# Reduction of domain flatness to rational-chart flatness

This module contains supporting results for
`PresentedAffinoidAlgebra.Domain.FlatnessStatement`. It does not prove that
statement by itself. It shows that the statement follows once the structural
map of every positive-radius rational chart is known to be algebraically flat.
Every result is stated for an arbitrary complete ultrametric normed field `K`,
with no condition on the valuation, the presentation radii, or the domain.

## Declarations

`RingHom.flat_of_finite_jointly_faithful` is pure commutative algebra. It
takes a ring map `φ : R →+* S` and a finite family of ring maps
`g i : S →+* C i`, and assumes three things: every `g i` is flat, every
composite `(g i).comp φ` is flat, and every maximal ideal `m` of `S` has some
`i` with `Ideal.map (g i) m ≠ ⊤`. It concludes that `φ` is flat. The ring
carriers can live in independent universes.

`PresentedAffinoidAlgebra.Domain.flat_baseMap_of_locus_eq` says that, for two
full represented domains `U V : Domain K A` with `U.locus = V.locus`,
flatness of `U.baseMap` implies flatness of `V.baseMap`. Here flatness means
Mathlib's `RingHom.Flat` for the underlying ring maps.

`PresentedAffinoidAlgebra.Domain.flat_baseMap_of_chartFlat` assumes that
`d.baseMap` is flat for every presented affinoid algebra `B` over the fixed
field `K` and every `d : RationalChart K B`. From this it concludes that
`U.baseMap` is flat for every `U : Domain K A`.

`PresentedAffinoidAlgebra.Domain.flatnessStatement_of_chartFlat` is the same
reduction with the field quantified as well. If every rational-chart
structural map over every complete ultrametric normed field `K : Type u` is
flat, then `Domain.FlatnessStatement.{u}` holds.

## Proofs

For `RingHom.flat_of_finite_jointly_faithful`, the proof gives `S` and every
`C i` the algebra structures defined by `φ` and `g i`. The product `Π i, C i`
is then flat over both `R` and `S`, because a finite product is linearly
equivalent to a finitely supported dependent function module, and Mathlib
proves that such modules are flat. The product is faithfully flat over `S`:
if a maximal ideal `m` satisfied `m • ⊤ = ⊤` there, its extension to the
product would be the unit ideal. Projecting that extension to the factor
`C i` chosen by the hypothesis would give `Ideal.map (g i) m = ⊤`, which
contradicts the choice of `i`. The Library lemma
`flat_of_faithfullyFlat_target`, applied to the tower `R → S → Π i, C i`,
then gives flatness of `φ`.

For `flat_baseMap_of_locus_eq`, the proof uses the bounded algebra equivalence
`boundedEquivOfLocusEq U V h : U.algebra ≃ V.algebra`. By
`boundedEquivOfLocusEq_comp_baseMap`, this equivalence carries `U.baseMap` to
`V.baseMap`. So `V.baseMap` is a flat map followed by a bijective ring map,
and it is flat.

For `flat_baseMap_of_chartFlat`, the proof starts from the Library's
`finiteRationalCover K A U`. This gives finitely many rational charts `D i`
over `A` and arrows `f i : (D i).toDomain ⟶ U` whose chart loci cover
`U.locus`. The proof applies `RingHom.flat_of_finite_jointly_faithful` to
`U.baseMap` and the bounded restrictions `(f i).restriction`, and checks the
three hypotheses:

- Composites. By `(f i).comp_baseMap`, `(f i).restriction` composed with
  `U.baseMap` is `(D i).baseMap`, which is flat by the chart hypothesis over
  `A`.
- Restrictions. `U.relative (D i).toDomain (f i)` regards the chart as a
  full domain over `U.algebra`, and its structural map is
  `(f i).restriction` by definition. `spectrumEmbedding K A U` shows that
  `U.spectrumMap` is injective. So `relative_locus_eq_preimage_of_injective`
  identifies the relative locus with the preimage of `(D i).locus` under
  `U.spectrumMap`. The pulled-back chart
  `RationalChart.pullback U.baseMap (D i)` over `U.algebra` has the same
  preimage as its locus, by `RationalChart.pullback_locus`. Its structural
  map is flat by the chart hypothesis over `U.algebra`, and
  `flat_baseMap_of_locus_eq` moves this flatness to the relative domain.
- Maximal ideals. For a maximal ideal `m` of `U.algebra`, the Library lemma
  `exists_spectrum_kernel_of_proper_ideal` gives a bounded multiplicative
  seminorm `x` on `U.algebra` whose kernel contains `m`. Its image
  `U.spectrumMap x` lies in `U.locus`, so it lies in some chart locus
  `(D i).locus`. Then `x` lies in the relative locus, which is the range of
  the spectrum map of `(f i).restriction`. So `x` is the pullback of a point
  `y` of `(D i).algebra`, and `m` is contained in the preimage of the kernel
  of `y`. If `Ideal.map (f i).restriction m` were the unit ideal, it would
  lie inside that kernel. This is impossible, because the kernel of a
  spectrum point is a prime ideal.

`flatnessStatement_of_chartFlat` introduces the field, the algebra and the
domain, and applies `flat_baseMap_of_chartFlat`.

## Provenance

These results are internal to the Library and are not taken from a
particular published proof. Berkovich, *Spectral theory and analytic geometry
over non-Archimedean fields* (1990), Proposition 2.2.4(ii) (printed
pp. 29–30 / PDF pp. 43–44), proves flatness differently. It handles the
strictly affinoid case over a nontrivially valued field with [BGR] 7.3.2/6,
then reduces the general case to it by extending the ground field. This
module avoids ground-field extension. Instead it combines the Library's
finite rational cover of a full domain (a Gerritzen–Grauert type statement)
with the standard fact that flatness descends along a faithfully flat
target. Flatness of the rational charts themselves is not proved here.
