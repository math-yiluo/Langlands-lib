# Smooth separation, admissibility and canonical bidual reflexivity

`Langlands.smoothAdmissibleDuality` proves the complete published proposition
`Langlands.SmoothAdmissibleDualityStatement`. The proof and every helper are
in this module. Worker 0 authored the Lean implementation and original proof
explanation; Worker 51 verified the published dependencies and expanded this
explanation. The Lean source is unchanged from Worker 0's supplied draft.

## Exact scope

The coefficient field is the complex numbers. The group and representation
space have independent universes `uG` and `uV`. The outer parameters are a group
`G` with a topology and a complex module `V`. The closing theorem introduces
the topological-group instance inside the target, followed by the hypothesis
that every open subgroup contains a compact open subgroup.

Under that cofinality hypothesis, the target contains both:

- For every smooth representation on `V`, canonical evaluation `smoothBidual`
  is injective.
- For every admissible representation on `V`, its smooth contragredient is
  admissible and canonical evaluation into its smooth bidual is bijective.

Admissibility includes smoothness and finite generation of the fixed vectors
for every open subgroup. Only those fixed-vector spaces are made
finite-dimensional. The representation space itself may be infinite-dimensional
and has no topology. The proof adds no Hausdorffness, local compactness,
countability, freeness or compactness hypothesis on the whole group. Supplying
compact-open cofinality for a particular group remains a separate obligation.

## Implemented argument

The private lemma `dual_smooth` proves that the smooth contragredient is smooth
for every representation. A smooth functional already carries an open fixing
subgroup; subtype extensionality transfers its fixing equations to the
restricted action. This lemma does not assume source smoothness.

`smoothBidual_injective_of_compact_cofinal` first shows that the kernel of
canonical evaluation is zero. For a vector in this kernel, source smoothness
provides an open fixing subgroup, and cofinality provides a compact open
subgroup `L` contained in it. Regard the vector as an element of `V^L`.
Surjectivity of `smoothDualFixedRestriction` extends every linear functional
on `V^L` to an `L`-fixed smooth functional on `V`. The kernel equation makes
its evaluation on the vector zero. Mathlib's `Module.eval_apply_injective`
therefore makes the vector zero. Applying this to a difference proves
injectivity. No admissibility or finite-dimensionality is used here.

`isAdmissible_smoothContragredient_of_compact_cofinal` applies the published
`isAdmissible_iff_of_cofinal` to the family of compact open subgroups.
Smoothness follows from `dual_smooth`. For each compact open `K`, restriction
injects the `K`-fixed smooth functionals into the algebraic dual of `V^K`.
Admissibility makes `V^K` finite-dimensional over the complex numbers, so its
dual is finite-dimensional. `Module.Finite.of_injective` transfers finite
generation to the fixed smooth functionals. The cofinal criterion then
supplies the condition for all open subgroups.

`smoothBidual_surjective_of_compact_cofinal` starts with a smooth bidual
functional `psi`. Choose a compact open subgroup `K` fixing it and put
`U = V^K`. Compact-open duality gives a restriction equivalence
`e : (V^vee)^K` to the algebraic dual of `U`. Restrict `psi` to `(V^vee)^K`
and compose with the inverse of `e`. This is an algebraic bidual functional
on the finite-dimensional space `U`; `Module.evalEquiv` supplies a vector
`u` representing it. The identity `Module.apply_evalEquiv_symm_apply` gives
agreement of canonical evaluation at `u` with `psi` on `(V^vee)^K`.

Equivariance of `smoothBidual` shows that evaluation at `u` is also fixed by
`K`. Injectivity of compact-open restriction, applied now to the smooth
contragredient representation, turns agreement on its `K`-fixed vectors into
equality of the two smooth bidual functionals everywhere. This second
application requires only `dual_smooth`, so surjectivity does not circularly
assume reflexivity or admissibility of the dual.

Finally, `smoothAdmissibleDuality` combines the three component theorems. The
`omit [IsTopologicalGroup G]` clause removes the ambient instance from the
closing theorem's outer parameters; the proof introduces that instance at
the target's internal binder. Smoothness and admissibility are likewise
introduced only where the proposition requires them. The canonical map is
the existing equivariant evaluation map throughout.

## Published imports and provenance

The three direct project imports are:

- `Langlands.Representation.Smooth.Contragredient.AdmissibleDualityStatement`,
  containing the exact target and the smooth dual and evaluation definitions.
- `Langlands.Representation.Smooth.Contragredient.CompactDualityProof`,
  containing `Langlands.smoothDualFixedRestriction_bijective`.
- `Langlands.Representation.Smooth.Admissibility.CofinalProof`, containing
  `Langlands.isAdmissible_iff_of_cofinal`.

All 26 Lean/Markdown files in their transitive project import closure were
compared with the published Library at
`15f4ec1bc9d27d00acfb08e2d8667e7b44317ee7` and matched byte for byte.
Their pairs are used unchanged. Mathlib's `LinearAlgebra.Dual.Lemmas` supplies
separation by algebraic duals and finite-dimensional bidual evaluation.
The environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

The original mathematical source is Bill Casselman, *Introduction to
admissible representations of p-adic groups*, Chapter II, revision June 16,
2019, Section 3, page 6: Proposition II.3.1, the following admissibility
paragraph, and Lemma II.3.2. The definitions are on page 2 and the stronger
ambient conventions on page 1. The original was read at those locations.
The complex specialization makes the finite fixed spaces free, as required
by II.3.2. Separation for all smooth complex representations is the derived
strengthening obtained from II.3.1 and algebraic separation; it is not quoted
as a separate assertion of II.3.2. Compact-open cofinality is the explicit
hypothesis used here in place of the chapter's stronger ambient conditions.

Registered original: `casselman-2019-smooth-representations`.
SHA256: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.

The restored proof passed an incremental Lake build with no warnings or errors.
Closing-theorem inspection reported independent levels `uG` and `uV` and exactly
the permitted standard axioms `propext`, `Classical.choice` and `Quot.sound`.
The development check does not itself perform a bound target comparison or
supply independent proof acceptance. Submission validation must compare the
complete theorem type with the Library proposition, and publication requires
independent semantic review.
