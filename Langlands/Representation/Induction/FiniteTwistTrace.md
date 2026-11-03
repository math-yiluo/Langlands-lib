# Finite character expansion of an induced Hecke trace

This is a derived construction on the existing smooth induction, compact
sections and integrated Hecke action. It combines the finite fixed-vector
model with the character coefficients of actual compact-section matrix
entries. It does not assert a new result from original literature.
Group, coefficient-carrier and finite-basis-index universes are independent.

Let `P` be a subgroup of a topological group `G`, let `sigma` be any complex
representation of `P` on `V`, and let `K` be a compact open subgroup of `G`.
A finite set `t` covers `G` by double cosets `P i K` and has distinct double
cosets. Write `H_i = conjOpenSubgroup P K i`, so its elements satisfy
`i^-1 p i` in `K`. Fix a finite basis `b`, indexed by `iota`, of

`U = product (i : t), fixedVectors sigma H_i`.

The basis is part of the construction's input. No admissibility or
finite-dimensionality of the whole inducing carrier is assumed. A finite
basis of this product will normally be supplied using admissibility and
compactness of the coefficient stabilizers.

For a character `chi : P ->* complex units` trivial on every `H_i`,
`twistFixedSpaceEquiv` identifies the fixed spaces for `twist chi sigma`
and `sigma` by the identical underlying vector. The action convention is
`(twist chi sigma)(p)v = chi(p) * sigma(p)v`. No inverse or conjugate
character is used. `fixedTwistEvaluationEquiv` combines these component
identifications with `fixedEvaluationEquiv` from
`Representation/Induction/FixedVectorModel`. Its forward map is actual
evaluation at the representatives. Its inverse, after forgetting fixedness,
is the finite sum of `twistedDoubleCosetSection` with the prescribed
component vectors. Both assertions are proved explicitly.

For `j : iota` and `y : t`, `fixedModelCoordinate P sigma K t b j y` is a
linear functional on the whole carrier `V`. It extends the restriction of
`b.coord j` to the `y` component by composing with the algebraic linear
left inverse of the fixed-subspace inclusion. The inclusion has zero
kernel, so this left inverse acts as the identity on that fixed subspace.
Consequently the sum of these component functionals on a vector of `U`
is exactly its `j`th basis coordinate. The extension is algebraic and
needs no carrier topology or continuous-dual assertion.

`inducedFixedTraceTwistCoefficients` is a finitely supported complex
function on the actual group `P`. For a right-`K`-invariant test function
`f` and a measure finite on compact sets, it is the sum over `j`, `y` and
`x` of `integratedCompactSectionTwistCoefficients`, with input vector
`b(j)(x)`, output representative `y` and functional
`fixedModelCoordinate ... j y`. It is chosen before `chi` and its support
and values have no character argument. Its direct compact-section
construction imports the universal, representation-independent finite
Hecke sampling from `Representation/Hecke/FiniteSampling`.

The theorem `inducedFixedTraceTwistCoefficients_eval` assumes a Borel
measurable structure, a left invariant measure finite on compact sets,
and left and right `K` invariance of `f`. Evaluation of the coefficient
function by `Finsupp.linearCombination` at `p |-> chi(p)` is the trace
on the actual `K`-fixed space of `smoothInduced P (twist chi sigma)` of

`integratedActionToFixed(f) composed with fixedVectors.subtype`.

The proof first sums the existing compact-section entry identity.
Linearity and the inverse evaluation formula convert the sum over input
sections to the actual integrated action on each inverse image of a
basis vector. Summing the extended output coordinates gives the diagonal
coordinate of the operator conjugated by `fixedTwistEvaluationEquiv`.
`LinearMap.trace_eq_matrix_trace` identifies their sum with the trace,
and `LinearMap.trace_conj'` gives the trace on the actual fixed space.
The basis and equivalence supply the finite model; the trace theorem
requires no admissibility premise. The inducing representation need not
be smooth, and `chi` need not be continuous; its stated stabilizer
triviality is precisely what this finite calculation uses.

Finally `induced_distribution_eq_twistCoefficients` assumes the standard
Hausdorff, locally compact and totally disconnected ambient group
conditions and actual admissibility of the twisted induced
representation. It applies `Character.distribution_eq_fixedVectors`
and the preceding identity to compute that representation's actual
distribution character by the same finite coefficient expression.
Admissibility is explicit and is not proved by this corollary.

These are fixed-level character identities. They do not by themselves
prove a density theorem for unramified parameters, a generic intertwining
equivalence, same-Levi induced-character equality, or the rational exact
finite-length K0 Weyl-conjugacy target. Actual reductive admissibility
and parameter realization remain separate obligations. No classification,
geometric lemma, adjointness, cuspidal-support theorem or character
independence theorem occurs in this construction or its proof.
