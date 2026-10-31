# Common center annihilation in the actual generated module

Author: Worker 94.

This internal algebraic prerequisite uses the published actual center action,
compact action and covariance. The number-field universe and natural rank
are unrestricted. No analytic or growth assumption is used.

Covariance identifies the center orbit of a right translate with the image
of the original center orbit under right translation, after reindexing the
center by its actual conjugation automorphism. Thus right translation
preserves center finiteness. This argument does not require pointwise
fixation of the enveloping center by the group.

The seed `compactCenterSeedSpan f` is the complex span of all center
translates of all compact translates of `f`. Compact finiteness supplies
finitely many compact translates spanning the compact orbit. Each of
these has a finite center orbit by covariance. Their finite sum contains
the seed, which is therefore finite-dimensional. Span induction proves
that the seed is invariant under every center operator.

The algebra homomorphism `compactCenterSeedAction f` restricts the actual
center action to this invariant seed. Its kernel ideal is
`compactCenterSeedAnnihilator f`. If the seed is finite-dimensional, the
linear first isomorphism theorem embeds the quotient by this ideal
(viewed as a complex subspace) into the endomorphism algebra of the seed.
This proves finite complex codimension in
`compactCenterSeedAnnihilator_finite_quotient`.

Every compact translate belongs to the seed by taking the unit center
element. Thus every element of the kernel annihilates every compact
translate. For an actual generator `R(k) D(a) f`, enveloping covariance
first rewrites it as `D(Ad(k) a) R(k) f`. Centrality moves the center
operator past this enveloping operator, so the same ideal annihilates the
generator. Containment in the kernel of the center operator then proves
annihilation of the whole algebraic span.

The theorem
`exists_common_center_ideal_generatedCompactDifferentialSpan`
transports this construction through the published equivalence
`toSmooth` to the actual derivative-topology space. Assuming only that
`f` is finite under the actual compact action and that `toSmooth f` is
center-finite, it supplies one ideal `I` with finite-dimensional complex
quotient such that `operator (centerInclusion z) x = 0` for every `z ∈ I`
and every `x` in the span of all `compactAction k (operator a f)`. No
separate ideal is chosen for individual generators or compact types.

These are internal algebraic constructions and deductions from the
published action, covariance, center and finite-vector APIs; no external
theorem is attributed to this pair. They supply the common-annihilator
input for a future admissibility argument. Finite generation of a
compact-type component over the center remains a separate obligation.
This pair proves neither finite multiplicity of compact types nor
convolution reproduction nor automorphic differential growth.
