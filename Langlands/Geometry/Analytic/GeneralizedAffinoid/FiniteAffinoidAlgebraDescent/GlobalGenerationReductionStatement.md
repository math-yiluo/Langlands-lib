# Effective finite Banach algebra descent from global generation

`Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraGlobalGenerationReductionStatement`
is an unproved proposition definition. It is an intermediate reduction
statement for the proof of `FiniteAffinoidAlgebraDescentStatement`, not an
axiom.

The inputs are those of `FiniteAffinoidAlgebraDescentStatement` (any complete
ultrametric normed field `K`, including trivially valued ones; an actual
presented positive-polyradius affinoid algebra `R`; a finite full-domain cover
`c` of `Domain.whole K R`; actual finite Banach local maps `F`; ordinary descent
data `d`), together with a natural number `n` and elements `s : Fin n →
d.toPairTransitions.MatchingAlgebra` of the constructed complete matching
algebra. The hypothesis is that, for every cover index `i`, the coefficient map
of the original local map `F.map i` at the projected tuple
`k ↦ projection i (s k)` is surjective, i.e. the projections of the `s k`
generate `F.algebra i` as a module over `(c.obj i).algebra`. This hypothesis is
exactly the conclusion of
`FiniteAffinoidAlgebraGlobalGenerationStatement`.

The conclusion is `Nonempty (EffectiveRealization d)`, the complete output
record of the target interface: a presented affinoid realization boundedly
equivalent to the matching algebra; `IsFiniteBanach` for the constructed
structural map from `R` and for its transport; bounded equivalences of the
closed-quotient base changes along every original cover restriction whose
forward maps are the constructed comparisons; exact overlap compatibility; and
the canonical homeomorphisms of the glued spectrum and of every inverse-image
locus.

No norm control on the generators is assumed: the local maps `F.map i` carry
their own `IsFiniteBanach` witnesses, and the statement leaves it to the proof
to obtain norm-controlled coefficients.

## Provenance

The statement isolates the second half of Kiehl's theorem: once the glued
module is globally generated on every member of the cover, it is a finite
module over the base whose base changes recover the local modules, and the
finite algebra is affinoid with the expected spectrum. Source: Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993), Kiehl's Theorem
and Remark 1.2.1(ii), printed p.15 / PDF p.12, and Lemma 1.2.12, printed p.20 /
PDF p.17 (registered source `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`). The
conjunction "this statement and `FiniteAffinoidAlgebraGlobalGenerationStatement`"
implies `FiniteAffinoidAlgebraDescentStatement` by applying this statement to
the generators supplied by the other one. The precise split into the two
statements is an internal derived formulation.
