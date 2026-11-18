# Global generation of finite Banach descent data by matching elements

`Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraGlobalGenerationStatement`
is an unproved proposition definition. It is an intermediate statement for the
proof of `FiniteAffinoidAlgebraDescentStatement`, not an axiom.

The inputs are exactly those of `FiniteAffinoidAlgebraDescentStatement`: a
complete ultrametric normed field `K` (trivial valuations allowed), an actual
presented positive-polyradius affinoid algebra `R`, a finite full-domain cover
`c` of `Domain.whole K R`, actual finite Banach bounded maps
`F.map i : (c.obj i).algebra → F.algebra i`, and ordinary descent data `d`
(pairwise bounded equivalences of the closed-quotient base changes over the
literal intersections, with identity and triple cocycle).

The conclusion: there are a natural number `n` and `n` elements `s k` of the
constructed complete matching algebra `d.toPairTransitions.MatchingAlgebra`
such that, for every cover index `i`, the coefficient map of the original local
structural map `F.map i` at the projected tuple `k ↦ projection i (s k)` is
surjective. In words, every element of the local algebra `F.algebra i` is a
linear combination `∑ₖ (F.map i) (aₖ) · projection i (s k)` with coefficients
`aₖ` in the original cover algebra `(c.obj i).algebra`. Only algebraic
surjectivity is asserted; no norm control is claimed here.

## Provenance

This is Theorem A for the coherent module defined by the descent data: the
global sections of the glued finite module generate it on every member of the
cover. It is the key step in Kiehl's theorem, Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), Kiehl's Theorem and Remark 1.2.1(ii),
printed p.15 / PDF p.12 (registered source `berkovich-1993-etale-cohomology`,
SHA256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`),
which states effective finite-module descent for finite affinoid covers in the
general (non-strict, possibly trivially valued) setting. The formulation via the
Library's already constructed matching algebra and `coefficientMap` is a
derived internal formulation chosen so that the companion statement
`FiniteAffinoidAlgebraGlobalGenerationReductionStatement` turns it into the
full effective realization.
