# Transport of continuation between actual compact models

Worker 200.

This is an internal construction from `CompactInductionModelChange`,
`CompactIntertwiningComposition`, and
`RationalUnramifiedOperatorContinuation`. It does not translate a new assertion
from the original literature. It constructs data for the compact realization
of the same actual ambient intertwiner family, using its actual extension and
restriction maps.

The field of scalars is the complex numbers. The ambient group, norm-character
index, and inducing carrier have independent universes. The construction works
for a locally compact nonarchimedean topological group, two semidirect
decompositions `P = M U` and `P' = M U'` with the same literal Levi subgroup,
and a canonical smooth inducing representation `A` of `M`. It requires the
displayed radical closedness and unimodular-modulus premises, closedness of both
parabolics, continuity of both Levi projections, and a continuous family of
positive norm characters of `M`.

The two compact open subgroups `K₀` and `K₁` are independent. Both are compact,
and each is supplied with both actual factorizations `G = P Kᵢ` and
`G = P' Kᵢ`. These are premises, not rational-point realizations established by
this construction. No inducing irreducibility, admissibility, finite length, or
finite-dimensionality is assumed.

Fix any parameter subset `Ω` and an actual family `J` of equivariant maps from
the normalized unramified induction for `P` to that for `P'`, defined at every
parameter of `Ω`. The input `p` is whole-operator rational continuation data
for the compact conjugations of `J` using `K₀`. In particular, it has one global
operator numerator polynomial in the existing finite regular expansion sense,
and one regular denominator nonzero throughout `Ω`, with the clearing identity
for every input vector.

Write `S(χ)` for the actual transition from the `P, K₀` model to the `P, K₁`
model, and `T(χ)` for the corresponding `P'` transition. Each extends to its
actual normalized induction and restricts to the other compact subgroup.
These transitions generally depend on `χ`. Their polynomiality, including
that of the inverse transition, is proved in `CompactInductionModelChange`;
it is not an additional premise here.

`compactModelContinuation` returns whole-operator continuation data for the
compact conjugations of the very same `J` using `K₁`. Its denominator is exactly
`p.denominator`, and its numerator is

`N₁(χ) = T(χ) ∘ p.numerator(χ) ∘ S(χ)⁻¹`.

The proof of numerator polynomiality composes the polynomial inverse transition,
the supplied polynomial numerator, and the polynomial target transition.
`IsPolynomialOperatorOn.comp` allows both factors to vary with the parameter,
so no fixed-map substitution or finite-dimensionality assumption is needed.
The clearing proof uses `compactIntertwiningOperator_modelChange` for the actual
ambient map `J(χ)` at `S(χ)⁻¹ f`. It cancels the source equivalence, substitutes
the original clearing identity, and moves the scalar through the linear target
transition. No comparison square is supplied as a hypothesis.

The denominator and numerator equations are recorded in
`compactModelContinuation_denominator` and
`compactModelContinuation_numerator`. The theorem
`compactModelContinuation_regularRegion` says that the chosen regular region
is unchanged. At each parameter there,
`compactModelContinuation_continuedOperator` identifies the new continued
operator with `T(χ) ∘ p.continuedOperator(χ) ∘ S(χ)⁻¹`, and
`compactModelContinuation_continuedOperator_natural` gives its commuting square.
These equations follow by expanding the reciprocal-denominator definition,
linearity of `T(χ)`, and the equivalence inverse identities.

This constructor retains the supplied continuation as a premise. It proves no
initial convergence or rationality theorem and requires no nonempty or open
parameter subset. For a standard integral family, its original domain must
already include all scalar convergence and original-carrier representability
conditions. This construction neither supplies those conditions nor changes
them. It compares the constructed continuation with the supplied one; comparison
of two independently chosen continuations and equality of canonical composite
scalars are separate obligations. It establishes no source-normalized `j` or
`mu`, nonvanishing, positivity, parabolic or measure independence, or Plancherel
conclusion.
