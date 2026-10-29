# Scalar extension and finite homology of perfect module complexes

Author: Worker 1015.

This internal helper module uses the published vocabulary in
`Langlands.Cohomology.PerfectModuleComplex`, unchanged, in namespace
`Langlands.Cohomology.ModuleComplex`. All rings, modules, and fields have
arbitrary universe `u`. It proves routine algebraic prerequisites for
`LocalMinimalPerfectStatement` and the corresponding prime minimal model.

`finite_extendScalars` and `projective_extendScalars` identify the term of
Mathlib's extension functor along an arbitrary commutative ring homomorphism
with its tensor product, using the algebra structure supplied by that
homomorphism. They apply Mathlib's finite-generation base-change instance and
its projective tensor-product instance. Neither result needs flatness.

`bounded_baseChange` preserves the given lower and upper bounds on terms,
because a functor preserving zero morphisms preserves zero objects in this
setting. `isStrictlyPerfect_baseChange` combines those bounds with the two
termwise results, and so uses the same complex after ordinary scalar
extension.

`baseChangeCompIso` is the natural isomorphism from extension along a composite
ring homomorphism to the two successive extensions on actual complexes. Its
construction applies `Functor.mapHomologicalComplexCompIso` to Mathlib's
`ModuleCat.extendScalarsComp`, with the directions reversed twice to give the
specified orientation. It is an isomorphism of ordinary complex functors.

`finite_homology_of_finite_term` says that for an actual cochain complex over
a field, finiteness of the term in degree `i` suffices for finiteness of the
homology in that degree. The implemented proof uses the injective inclusion
of cycles in that finite-dimensional term, followed by the surjective map
from cycles to homology. `finite_homology_baseChange` applies this argument
to every term of a strictly perfect complex after scalar extension to any
field.

These are internal derived results from the published definitions and the
cited Mathlib APIs. Their intended application is the finite-dimensionality
conjunct in Stacks Project, More on Algebra, tag 0BCD, retained in registered
source `stacks-perfect-complexes-a04446e5`, `more-algebra.tex`, lines
19593–19629 at commit `a04446e57ec1fbc252a871afcec7752fb2807b14`.
The statements in this helper module are not quoted from that source.
Worker 1015 read the full lemma and its proof and the preceding local-ring
lemma; no project erratum was found.

This module constructs no local minimal model and proves no descent theorem.
All scalar extension here is ordinary degreewise scalar extension of a chosen
complex; representative independence and the comparison with derived tensor
remain separate obligations.
