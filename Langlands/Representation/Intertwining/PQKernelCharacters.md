# Action kernels and generalized characters

Author: Worker 154. Module `Langlands.Representation.Intertwining.PQKernelCharacters`,
namespace `Langlands.PQKernelCharacters`.

`characterAlgebraHom χ` extends a complex group character `χ : B → ℂˣ`
to the scalar algebra homomorphism `ℂ[B] → ℂ`. The companion lemmas prove
that the occurrence of `χ` as a generalized eigencharacter forces the whole
action kernel into this scalar character kernel, and that comaximal action
kernels therefore give disjoint generalized-character sets.

## Source and provenance

The motivating source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version of 9 July 2026, VII.3.3, proof of the regularity
Lemma, printed pp.234–235 / PDF pp.240–241. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 154 read both PDF pages. The source extends group characters to their
algebra homomorphisms and uses containment of action kernels in character
kernels for the implication to exponent disjointness. The provenance is
derived: the Lean module proves this algebraic step for arbitrary complex
representations of a commutative group, with independent carrier universes.

There is no topology or finite-length premise. Generalized occurrence is the
published `IsGeneralizedEigencharacter` predicate: a nonzero vector is killed
by one common power of every operator `ρ(b) - χ(b)`. No open-kernel condition
on `χ` is required for these algebraic assertions.

## Implemented proof

The scalar extension is Mathlib's `MonoidAlgebra.lift` of the character
followed by the inclusion of complex units into the complex numbers.
`mem_maxGenEigenspace_action` fixes a vector in a finite uniform character
space and uses linear induction on a group-algebra element. At zero the
claim is immediate. At a single group element times a scalar it uses
`Module.End.genEigenspace_le_smul`. For a sum it uses
`Module.End.genEigenspace_inf_le_add`; the two operators commute because
the group algebra is commutative. These assertions are applied to maximal
generalized eigenspaces (exponent infinity), so the resulting finite power
may depend on the group-algebra element. A uniform power for all elements
of the algebra is neither needed nor asserted.

For `kernel_le_characterKernel`, choose a nonzero generalized-character
vector. If the group-algebra element acts by zero, the previous lemma says
that some power of its scalar character value kills this vector. A nonzero
complex scalar and each of its powers act injectively, so the character
value must be zero. Thus the actual action kernel is contained in the
kernel of `characterAlgebraHom χ`.

Finally `disjoint_generalizedCharacters` supposes that `χ` occurs in both
representations. Their action kernels are then contained in the same
scalar character kernel, so their sum cannot contain 1: the character sends
1 to 1. This contradicts comaximality and proves disjointness.

## Retained application obligations

This auxiliary unit supplies the algebraic implication from comaximal action
kernels to disjointness in VII.3.3. The exact
`PQRegularityLemmaStatement` additionally needs the geometric support
filtration and its grade identifications, comparison with the published
compact-open weight predicate, and the finite-length converse. None of
these is asserted here; no full target statement is modified.

The imports are the unchanged `Intertwining.PQRegularity` (the actual action
kernel) and `Exponents.Jacquet` (the generalized-character predicate).
