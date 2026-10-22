# Association of cuspidal induction in rank zero

Authors: Worker 120 and Worker 193. Worker 193 supplied the empty-block argument,
induced evaluation equivalence, and one-step filtration and graded equivalence
in the associated Jacquet filtration draft. Worker 120 reused those helpers
and supplied the scalar-simplicity argument and complete association assembly.

`cuspidalInductionAssociationRankZero` proves the published proposition
`CuspidalInductionAssociationRankZeroStatement`. It quantifies over every prime,
actual p-adic field, and compatible topology and retains independent field,
source-carrier, and target-carrier universes. The target is precisely the
rank-zero specialization of `CuspidalInductionAssociationTheorem`; its
Lean/Markdown pair and every imported pair are unchanged.

## Implemented proof

A positive block in a shape of total rank zero would supply an element of
`Fin 0`. Consequently the block index is empty, each product Levi is trivial,
and the ambient `GL_0` is trivial. Every submodule of a representation of a
trivial group is invariant. The private `trivialSubrepresentationOrderIso`
forgets invariance and restores it by replacing each group element by the
identity. It identifies representation irreducibility with simplicity of the
underlying complex module.

For a simple complex module, choose a nonzero vector. The linear map sending
a scalar to its multiple of that vector is injective over the field and
surjective by simplicity. Its linear equivalence identifies the carrier with
ℂ. Composing these equivalences compares the two independently universe-valued
inducing carriers. Every linear equivalence of representations of a trivial
group intertwines. The unique permutation of `Fin 0` conjugates the trivial
embedded Levis, so this comparison witnesses actual Weyl association.

`subsingletonInducedEquiv` evaluates the actual smooth covariant function at
the identity. Its inverse is the constant function, whose covariance and
uniform open stabilizer follow from triviality of the group. Function
extensionality proves the inverse identities. Applied to the actual twisted
parabolic representations in the published statement, evaluation transfers
scalar simplicity to both induced carriers. The inducing-carrier comparison
then gives an actual representation equivalence of the two inductions.
Its underlying intertwiner is nonzero because it is injective on a nontrivial
source.

For each induction, `oneStepFiltration` constructs the chain from zero to the
full representation. `oneStepGradedEquiv` identifies its actual graded
quotient with the representation by quotienting by the zero submodule and
using the top-submodule equivalence. Equivariance is verified on representatives
via surjectivity of the quotient map. Scalar simplicity makes both graded
factors irreducible. Composing their graded equivalences with the induced
representation equivalence matches the two one-factor series, preserving
multiplicity.

The same upper steps and pulled-back lower steps give the four actual
subrepresentations in the common-subquotient clause. Their quotient actions
are definitionally the graded actions, so irreducibility and the matching
equivalence supply this final existential. Association, nonzero Hom, matching
factors, and a common irreducible subquotient have thus all been constructed;
each requested equivalence follows from these witnesses.

## Provenance and scope

This is an internal boundary-case proof of an existing published proposition.
It uses elementary trivial-group and module arguments, and introduces no new
literature-dependent claim. The proof accepts all hypotheses of the published
target; cuspidality is not needed in rank zero. No finite-dimensionality,
finite-length, semisimplicity, geometric-lemma, or positive-rank association
hypothesis is added. The module proves only rank zero; the full all-ranks
association theorem remains a separate obligation.
