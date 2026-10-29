# Scalar generalized-character detection

Authors: Worker 561, Worker 846 and Worker 438.

This module proves the published proposition
`Langlands.ScalarGeneralizedEigencharacterDetection.{uG,uC,uV}` by the theorem
`Langlands.scalarGeneralizedEigencharacterDetection`. The group, character-group
and vector-space universes remain independent. The proof is internal elementary
linear algebra about the published predicates, rather than a theorem quoted from
original literature. Workers 561 and 846 supplied the shared proof draft; Worker
438 separated its two entry modules and checked their exact signatures.

The helper `Langlands.scalar_generalized_character_eq` applies
`isGeneralizedEigencharacter_iff` to obtain a common natural-number power `k`
and a nonzero vector `v`. The prescribed scalar action along `z` identifies
`(ρ.comp z) c` with `(ω c : ℂ) • 1` as complex-linear endomorphisms. Thus the
common-power equation becomes
`((ω c : ℂ) - (χ c : ℂ)) ^ k • v = 0`. The field property and `v ≠ 0` force
the scalar power to vanish. `eq_zero_of_pow_eq_zero` then forces its base to
vanish, and extensionality gives `χ = ω`. This inference handles all powers,
including `k = 0`, for which a nonzero witness cannot exist.

For `Langlands.scalar_generalized_character_iff`, the forward implication uses
that equality lemma. In the reverse direction, the additional `Nontrivial V`
premise supplies a nonzero vector. Scalar action makes it an ordinary
eigenvector for `ω`, so `isGeneralizedEigencharacter_of_eigenvector` applies.
The closing theorem packages these two helpers in precisely the conjunction
of the published target. Nontriviality is used only for the target's second
clause; the equality helper extracts its nonzero vector from generalized
occurrence itself.

The reusable helper `Langlands.isGeneralizedEigencharacter_comp` restricts a
generalized eigencharacter along an arbitrary monoid homomorphism. It keeps
the same nonzero vector and the same power and evaluates the old equations
at the image elements. It uses neither surjectivity nor a group hypothesis.

The only direct import is the published statement module. No finite dimension,
finite length, admissibility, smoothness, centrality, commutativity, continuity
or open-kernel premise is added. Neither the proof nor the statement's import
closure uses segment square-integrability, Casselman criteria, derivative
results or downstream classification/exhaustion theorems.
