# Algebraic distributions and homeomorphism transport

`Langlands.HarmonicAnalysis.Distribution X` is the algebraic complex dual of
`SchwartzBruhat X`, the existing space of locally constant, compactly supported
complex functions. Neither this test-function space nor its dual is given a
topology here, and no continuity condition is imposed on the functionals.

For an actual homeomorphism `e : X ≃ₜ Y`, `Distribution.pushforward e` is a
complex linear equivalence from distributions on `X` to distributions on `Y`.
Its defining formula is `(e_* D)(f) = D(f ∘ e)`. The implementation precomposes
`D` with the existing `Hecke.TestFunction.pullback e`; that construction
already proves local constancy and compact support. The inverse precomposes
with pullback by `e.symm`. Evaluation and extensionality prove the inverse,
identity and covariant composition laws. The source, intermediate and target
spaces may lie in independent universes. No Haar measure or modular factor
is used.

On a topological group, `conjugationHomeomorph a` is the actual map
`x ↦ a * x * a⁻¹`, constructed by composing left and right translation.
`IsConjugationInvariant D` is a proposition asserting `a_* D = D` for every
such map. The proved characterization says this is equivalent to
`D(f ∘ conjugationHomeomorph a) = D(f)` for every `a` and every test function.
The equivalence follows by evaluation in one direction and linear-map
extensionality in the other.

## Source correspondence and scope

Bernstein and Zelevinsky, *Representations of the group GL(n,F), where F is
a non-Archimedean local field (survey)* (1976), Section 1.7, printed/PDF p.7,
defines the algebraic distribution space without a topology. Section 1.17,
printed/PDF p.10, transports test functions from `X` to `Y` by composition
with the inverse homeomorphism and defines distribution transport dually.
Consequently its distribution pushforward is exactly the formula above.
The conjugation specialization is the action used in Section 7.3,
printed/PDF pp.57–58. The registered source is
`bernstein-zelevinsky-1976-representations-gln`.

The source works with locally compact, totally disconnected Hausdorff spaces.
This module's elementary constructions apply to any topological space because
the existing test functions and homeomorphism pullback need no additional
hypotheses; this is a direct generalization of those definitions, not a claim
that the source states the greater generality. The inverse, composition and
invariance characterizations are internal algebraic consequences implemented
as described above. No assertion about transpose invariance of invariant
distributions, representation characters or Gelfand–Kazhdan equivalences is
proved here.
