# Integral lattices with a specified basis

This module implements concrete finite integral combinations using Mathlib's
`Finsupp`. It is a generic prerequisite for Henniart's two local virtual groups.
It does not yet instantiate either the local irreducible Weil classes or the
local supercuspidal classes, and does not define the Grothendieck group of
finite-group representations. Those remain separate required constructions.

`IntegralLattice I` is exactly `I →₀ ℤ`. Its actual basis, generators, coefficient maps,
linear and bilinear extensions, pushforwards and reindexing equivalences all
reuse Mathlib. An arbitrary map pushes coefficients forward by adding coefficients
over a fiber; a genuine equivalence gives a linear equivalence. An explicit
natural-number weight gives an integer-valued degree. Virtual degree can be
negative. The integral pairing is the finite coefficient dot product, obtained
by extending the coefficient functionals. It does not assume any character
orthogonality or local-factor identity.

The additive submonoid `effective` consists of coefficientwise nonnegative
elements. A support subset gives a submodule, identified concretely with finite
combinations on that subset. Thus the unitary sublattice can later be obtained
from a genuine unitary predicate, without declaring an arbitrary predicate to be
unitarity. A supplied family generates its integral span; `evaluateGenerators`
maps formal combinations into that span with its membership fields proved.
`relations` is the kernel of the family's linear evaluation.
`generatedPairs` records the span of pairs arising from a common family, without
asserting either projection is injective or selecting a correspondence.

`RankedBasis B` is the dependent disjoint union of `B n` over positive integers.
The ranked lattice retains the rank label, with inclusion and coefficient
restriction for every rank, the rank-weighted degree, and a supported submodule
for each basis rank. A total-degree stratum is different from support in a
single rank. Neither that stratum nor an effective-degree stratum is declared
finite. `basisStratum` further fixes a supplied invariant. Rank-preserving
equivalences act by reindexing. An already constructed group action on a basis
has an actual orbit quotient and the induced map collecting coefficients.
No action of local characters is invented here.

The basis, other index types, and target module have independent universes.
Coefficients are exactly the integers; no topology or field is used.
Construction fields follow from the reused Mathlib maps and submodules;
the effective cone's closure follows from addition of nonnegative integers.

## Source correspondence and boundaries

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
p-adique* (2000), sections 2.5–2.6, pp. 445–447, defines the two free integral
groups, the spans of global images, degree, and orthonormal-basis pairings.
Section 2.8, p. 448, uses integral relations among the global images; section
3.7, p. 451, uses the span of actual induced characters.
Source ID: `henniart-2000-simple-proof`; retained PDF SHA256:
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
These passages were read in the retained original. The present arbitrary-basis
constructions are a derived generalization of their elementary integral-linear
algebra. The names `generated` and `generatedPairs` describe their actual inputs;
they do not claim a family of arbitrary functions is a global automorphic object.

Mathlib revision `5ed2965256430c3649e86755f9576b54eca72435` supplies:
`LinearAlgebra/Finsupp/LinearCombination.lean` (`linearCombination`);
`LinearAlgebra/Finsupp/Defs.lean` (`lapply`, `lmapDomain`, `lcomapDomain`);
`LinearAlgebra/Finsupp/LSum.lean` (`domLCongr`);
`LinearAlgebra/Finsupp/Supported.lean` (`supported`, `supportedEquivFinsupp`);
`LinearAlgebra/Finsupp/VectorSpace.lean` (`basisSingleOne`);
and `GroupTheory/GroupAction/Defs.lean` (`orbitRel`).

No project artifact is imported. Later modules must supply the actual two local
bases, their twists and duals, the unitary subsets, induced-character families,
and weak-association families. IntegralLattice spanning, isometry, finiteness, and the
norm-one/positive-degree argument are separate theorem obligations. In
particular the automorphic basis must consist of supercuspidal classes across
positive ranks, not all irreducible GL_n representation classes.

Author: Worker 24.
