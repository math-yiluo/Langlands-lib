# A short exact sequence from a last grade and a single surviving prefix grade

Author: Worker 124.

This internal module proves
`Langlands.smooth_shortExact_of_last_and_single_prefix`. Let `A`, `B`, `C` be
smooth representations of any topological group over a commutative ring, with
independent coefficient, group and carrier universes. Suppose `s` is an actual
`ObjectRepFiltration A.obj (n + 1)`, `q₀ : Fin n`, the grade at `q₀.castSucc` is
isomorphic to `B.obj`, the last grade is isomorphic to `C.obj`, and every other
prefix grade has subsingleton carrier. The conclusion gives actual intertwining
maps `B → A → C` satisfying `SmoothRep.IsShortExact`: injectivity, surjectivity
and equality of the linear range with the kernel. Neither `B` nor `C` is
assumed irreducible or nonzero. The statement also imposes no finite length.

The proof evaluates the published `RepFunctorFiltration.initialFiltration` on
the singleton object. `singleSurvivingGradeIsoAt` and `prefixGradedIso` identify
the penultimate subrepresentation with `B.obj`. The inverse of this isomorphism,
followed by the actual inclusion of the penultimate step, gives the first map.
The published `lastProjection`, followed by the last-grade isomorphism, gives
the second map. The isomorphisms preserve injectivity and surjectivity.
For exactness, the proof compares the first map's range with the actual
inclusion's range, and the second map's kernel with the actual last projection's
kernel. `range_penultimate_eq_ker_lastProjection` identifies those middle
submodules.

This is a derived algebraic consequence of the existing finite-filtration
constructions, not a claim taken independently from literature. Dependencies are
`RepFunctorFiltration.initialFiltration`, `prefixGradedIso`,
`lastProjection`, `lastProjection_surjective`,
`range_penultimate_eq_ker_lastProjection` from
[Splicing](Splicing.md), `singleSurvivingGradeIsoAt` from
[SingleSurvivingGrade](SingleSurvivingGrade.md),
`RepSubfunctor.inclusion_injective`, and `Representation.equivOfIso`.
The single-grade collapse in turn uses the published zero-factor-deletion and
length-one quotient comparisons. The proof uses no representation-theoretic
geometric lemma, adjointness, classification or cuspidal-support theorem.
It constructs maps in a specified order; it does not reorder an existing
filtration or assert that a representation splits as its graded object.
