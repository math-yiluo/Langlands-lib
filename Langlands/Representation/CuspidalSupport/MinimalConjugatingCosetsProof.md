# Minimal conjugating permutations and right block-Weyl cosets

Author: Worker 165.

This module proves the published
`Langlands.CuspidalSupport.MinimalConjugatingCosetsTheorem` from
`Langlands.Representation.CuspidalSupport.JacquetInductionStatement`.
The closed proof is `minimalConjugatingCosetsTheorem`. For each permutation
`w` conjugating the actual embedded Levi of `B` onto that of `C`, it gives
exactly one `v : MinimalConjugatingPermutations B C` for which
`w = v.val.val * b.val` for some `b : blockWeyl B`.

The proof imports `Langlands.Geometric.weylDoubleCoset_bijective` from
`Langlands.Representation.Geometric.WeylMinimalRepresentativeProof`.
This is Worker 243's published existence and bijectivity result, which uses
Worker 175's published uniqueness proof. No chosen parametrization or
bijectivity hypothesis is an input to either theorem proved here.

## Implemented argument

The matrix helper `levi_mem_iff` characterizes the embedded Levi by zero entries
between different coordinate blocks. In the reverse direction those zero entries
put the matrix in the standard parabolic. Its Levi projection, embedded back
into the ambient group, has the same diagonal blocks and the same zero off-block
entries, so it recovers the matrix. The coordinate identity `blockIndex_index`
is imported from `WeylDefinitions`.

`permutation_mem_levi_iff` identifies membership of a permutation matrix in the
embedded block Levi with preservation of every coordinate block index. In one
direction the entry in row `w a`, column `a`, is one, so those coordinates must
be in the same block. In the other direction, every nonzero permutation-matrix
entry lies inside one block. The private zero-pattern lemma needs only a
commutative ring; the permutation-matrix equivalence additionally requires
that ring to be nontrivial.

For fields, the private composition, inverse, and membership lemmas express
actual Levi conjugation using subgroup maps. Elements of the block Weyl group
have permutation matrices in the Levi, so they normalize it.
`conjugatesLevi_weyl_mem` consequently restricts actual Levi conjugation to the
block Weyl groups.

Surjectivity of the imported `weylDoubleCoset_bijective B C` supplies a minimal
double-coset representative `v` of a conjugating `w`.
Left and right block-Weyl multiplication preserves the Levi-conjugacy property.
Thus `v` is also a conjugating permutation. The double-coset equation
`w = a * v * b` can be rewritten as
`w = v * ((v⁻¹ * a * v) * b)`; the factor in parentheses belongs to the source
block Weyl group. Uniqueness follows from injectivity of the minimal double-coset
map, since a right-coset factorization supplies equality in the double quotient.
The implementation uses this argument in `minimalConjugatingCosets`.
It proves uniqueness of the actual subtype element `v`, including its
minimality and conjugacy conditions, by subtype extensionality and the
imported injectivity.

## Scope and dependency

The closed theorem retains every prime, every actual p-adic field,
every positive rank, every ordered positive source and target block shape,
and every permutation conjugating the actual embedded Levis. Its type is
exactly the published proposition, with no supplied coset parametrization
or additional hypothesis. The statement and its imports are unchanged.

The reusable theorem `minimalConjugatingCosets` proves the same conclusion
over any field and at every natural rank, including zero. The closed
p-adic theorem specializes it to `F.Carrier`; the positive-rank hypothesis
is retained in the statement but is unnecessary for this stronger helper.
The result fixes both source and target block shapes. It does not assert a
total count over all target shapes or construct a block-reordering equivalence.

## Provenance

The original target is the GL specialization of the coset identity in Bernstein
and Zelevinsky (1977), proof of Corollary 2.13(c), printed page 449 (PDF page 10),
using Lemma 2.11(a), printed page 448 (PDF page 9). These original pages were
read directly. Source ID: `bernstein-zelevinsky-1977-induced-i`; SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The matrix lemmas are internal consequences of the existing concrete definitions;
the group-theoretic reduction implements the coset identity used in that proof.
