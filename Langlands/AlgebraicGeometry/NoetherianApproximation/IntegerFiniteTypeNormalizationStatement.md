# Finite normalization of finitely generated integer domains

`Langlands.AlgebraicGeometry.NoetherianApproximation.IntegerFiniteTypeNormalizationStatement.{u}`
states that for every commutative domain `A : Type u` finitely generated as a
ℤ-algebra, its integral closure in `FractionRing A` is a finite `A`-module.
The ℤ-algebra is canonical. The universe is arbitrary; there is no assumption
on characteristic, dimension, normality, or separability. This file states
propositions and supplies no proofs.

This is a derived consequence of the registered Stacks source
`stacks-normal-finite-type-subalgebras-2026-11-01`, folder SHA256
`28b191f332990a0874602649e0970a933c9d769a8ce979d1177ea3f3823ab55d`.
[Proposition 10.162.16](https://stacks.math.columbia.edu/tag/032E)
includes ℤ among Nagata rings and includes their finite type extensions.
Proposition 10.162.15 identifies these with Noetherian universally Japanese
rings. Thus a finite type integer domain is N-2, and in particular N-1 by
taking the degree-one extension of its own fraction field.
[Definition 10.161.1](https://stacks.math.columbia.edu/tag/032F)
defines N-1 precisely by the module finiteness expressed here. The retained
source files are `032E.html` and `032F.html` in the registered snapshot.
The source comments contain no correction to these cited claims; there is
no project errata file for this source in the current Library.

`IntegerFiniteTypeNormalizationReductionStatement.{u}` is an internal
reduction statement: the preceding universal finiteness proposition implies
the published `NormalFiniteTypeSubalgebraStatement.{u}` at the same universe.
It does not itself provide that finiteness premise. Its provenance is the
construction explained in the published target's Markdown: for
`A = ℤ[s] ⊆ R`, embed the normalization of `A` in `Frac A` into `Frac R`.
Integral closedness of `R` places its image inside `R`. The image is normal,
contains `s`, and is finite type over ℤ; finite generation then implies
noetherianity. Normality of integral closure is supported by
[Lemma 10.37.2](https://stacks.math.columbia.edu/tag/037B), in retained
`037B.html`. The reduction is an internal interface for this construction,
not a numbered assertion in the source.

The finiteness proposition concerns normalization in `Frac A`. It makes no
claim about the integral closure in the fraction field of a larger ambient
ring. The reduction's conclusion is exactly the already published proposition
and includes an actual ℤ-subalgebra of that ambient ring with all four
prescribed properties.
