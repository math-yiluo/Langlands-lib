# Finite continuous coefficients for actual enveloping conjugation

Author: Worker 88.

`Langlands.Global.ArchimedeanGL.EnvelopingConjugationCoefficientsStatement`
defines a proposition for every `K : Type u` with `[Field K] [NumberField K]`
and every `n : ℕ`, including zero. This module states the proposition; it
does not prove it.

## Exact assertion

Write `G = InfiniteAdelicGL K n` and `U = EnvelopingAlgebra K n`. For every
`a : U`, there exist a natural number `m`, a family `b : Fin m → U`, and a
family `c : Fin m → C(G, ℂ)` such that, for every `g : G`,

```text
envelopingConjugation K n g a = ∑ i : Fin m, (c i g) • b i.
```

The choices of `m`, `b`, and `c` may depend on `a`; all three are chosen before
`g` is quantified. In particular, the elements `b i` are fixed across the
entire group. Each `c i` is a globally continuous complex-valued function,
not merely a coefficient chosen separately at each group element. The family
`b` is not required to be linearly independent, and `m = 0` is allowed.
The sum and complex scalar multiplication are those of the actual enveloping
algebra.

Here `G` is the existing matrix general linear group over
`NumberField.InfiniteAdeleRing K`, the product of the actual archimedean
completions. It carries its existing matrix-units topology, and `ℂ` carries
its usual topology. The statement introduces no topology on `U` and assumes
no replacement action, finite-orbit property, continuity premise, positive
rank, or connectedness.

## Imported constructions and internal provenance

This is an internal algebra and topology statement formulated against
`Langlands.Global.ArchimedeanAdjoint`, which imports the actual adelic group
definitions in `Langlands.Global.AdelicGL`. It is not presented as a verbatim
assertion from external literature.

The imported `envelopingConjugation` is the complex algebra automorphism
obtained by lifting `complexLieConjugation` through the universal enveloping
algebra. Its convention is `Ad(g)X = g X g⁻¹` on real matrix coordinates,
as recorded by `realLieConjugation_apply`. The imported
`complexLieConjugation_tmul` extends this map by the identity on complex
tensor coefficients, and `envelopingConjugation_generator` identifies its
action on the canonical enveloping generators. Thus the left side of the
assertion uses the existing concrete automorphism.

A possible later proof can choose a finite real basis of
`ArchimedeanMatrix K n`, express actual matrix conjugation in that basis
with continuous coefficients, and transport the formulas through
`realLieAlgebraToMatrix` and the complex tensor generators. Algebra
generation can then extend the finite-expansion property under sums, scalar
constants, and products. This describes an intended proof route, not a
proof implemented in this statement module.

The intended application is to express varying conjugated differential
operators using finitely many fixed enveloping elements. Differential
covariance and continuity of the smooth right action are separate
obligations; neither is asserted or proved here. The final Lean example
checks only the full parameter type of the proposition.
