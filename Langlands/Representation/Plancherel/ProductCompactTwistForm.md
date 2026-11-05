# Hermitian compatibility of the actual compact twist comparison

This derived construction supplies the coefficient-level Hermitian
compatibility needed for the fixed compact picture in Waldspurger VI.1,
printed pp.295–296 / PDF pp.61–62. The inducing and smooth-dual forms are
those in V.2, printed p.293 / PDF p.59, from the registered original source
`waldspurger-2003-plancherel`. The original compact comparison retains
vectors and the underlying linear functionals. The construction below
proves preservation of their actual coefficient-tensor form when the
character is unitary; it does not assume this preservation as new data.

The first three lemmas apply to any topological group, any complex
representation with a supplied positive invariant form, and any character
with open kernel and norm one at every group element. The representation
is admissible and compact open subgroups are cofinal. The group and
representation carrier have independent universes. No topology or
finite dimensionality is imposed on the whole representation carrier.
The admissibility of the twist follows from the published
`isAdmissible_twist_iff`.

`InvariantPositiveForm.smoothDualEquiv_twist` says that the actual
smooth-dual twist equivalence, applied after the conjugate-linear
Hermitian identification for the twisted form, is the original
Hermitian identification. Both functionals evaluate on a vector as
`b.inner v w`: the unitary twist keeps the underlying form and the
smooth-dual comparison keeps the functional. Subtype and linear-map
extensionality prove the identity.

`InvariantPositiveForm.smoothDualEquiv_twist_symm` applies injectivity of
the original Hermitian identification and its inverse identities to show
that the inverse identifications return the same vector.
`HarishChandraSchwartz.dualInvariantForm_twist_inner` then expands the
actual dual forms and applies this inverse identity in both arguments.
The reversal of the two arguments in the dual form is retained.

The remaining constructions specialize to the existing family of
unramified characters of a subgroup of a nonarchimedean topological
group. The character is an element of `unramifiedCharacters ν` with the
additional explicit norm-one condition; together these are precisely
the two membership conditions in `unitaryUnramifiedCharacters ν`.
The published open-kernel theorem supplies smoothness of the character.
The positive invariant form and admissibility belong to the inducing
representation, which need not be irreducible.

`productCompactTwistTensorEquiv_inner` proves preservation of the entire
coefficient-tensor form by the already published
`productCompactTwistTensorEquiv`. Double algebraic tensor induction
reduces this identity to pure tensors. There it is the product of the
unchanged original inner product and the proved dual-form comparison.
Additivity handles the induction steps.
`productCompactTwistTensorIsometry` bundles this same existing linear
equivalence with its proved inner-product identity as a subtype.
Its underlying linear equivalence is unchanged.

No full product-Levi equivariance of the untwisting map is claimed.
This unit precedes integration and uses no Haar measure or formal
degree. Comparison of the actual induced source with its fixed compact
form, inverse-degree normalization and the spectral family form remain
further consumers. No structural realization on all reductive rational
points, wave-packet assertion, Plancherel isometry or completion of a
whole-task condition follows from these constructions.
