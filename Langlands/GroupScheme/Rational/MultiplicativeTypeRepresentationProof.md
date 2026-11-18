# Representations of multiplicative-type groups: the Galois-orbit theorem

Workers 537 and 666, with stable-subspace and projection support by Worker 539.

`Langlands.GroupScheme.multiplicativeTypeRepresentationGaloisOrbit.{u}` proves
the unchanged published
`Langlands.GroupScheme.MultiplicativeTypeRepresentationGaloisOrbitStatement.{u}`.
It has no additional hypotheses. The proof applies over every field, to every
affine group scheme of multiplicative type, and to every separable closure in
the stated universe. It imports the original target without modifying it.

## Implemented proof

The final proof assembles five component theorems:

1. `isSemisimple_of_isMultiplicativeType` proves the exact sum-of-simple-stable-
   subspaces formulation. Over a separably closed extension, the group is
   diagonalizable. Its universal group-algebra coefficient columns span and are
   actual character vectors, including when the character group has torsion.
   Every subspace of a character space is stable. Stable projections and
   entrywise linear-functional descent then descend semisimplicity to the
   original field.
2. `exists_weights_eq_galoisOrbit_of_isMultiplicativeType` proves that the
   nonzero character spaces of an irreducible representation form one orbit.
   Coefficientwise Galois conjugation carries the `χ`-space to the conjugate
   character space. A single orbit sum descends to an original stable subspace,
   so irreducibility makes it the whole representation. Independence excludes
   weights outside the orbit.
3. `exists_irreducible_weights_eq_galoisOrbit_of_isMultiplicativeType` realizes
   every orbit. The universal tensor value of any geometric character and
   local finiteness of original affine matrix coefficients force that character
   to occur in the scalar extension of some original finite representation.
   Semisimplicity supplies a simple subrepresentation retaining the character;
   the single-orbit result identifies all of its weights.
4. `isomorphic_iff_weights_eq_of_isMultiplicativeType` proves uniqueness.
   A common weight gives a nonzero intertwiner over the separable closure,
   which has a nonzero original-field linear coefficient. Actual irreducibility
   makes that intertwiner bijective. Conversely a bijective actual intertwiner
   and its inverse identify every character space.
5. `exists_fixedField_endomorphismAlgHom_of_isMultiplicativeType` identifies the
   endomorphism algebra. The minimum-support argument produces a normalized
   character vector fixed by its stabilizer. Its conjugate lines span by
   irreducibility, and character projection proves the character space is one
   line. Each element of the stabilizer fixed field gives an equivariant scalar
   on the orbit, and the corresponding diagonal operator descends to an actual
   original-field endomorphism. Its action on conjugate lines proves the
   algebra laws and injectivity. Every actual endomorphism preserves the
   normalized character line; its scalar there is stabilizer-fixed, and
   spanning conjugate lines identify it with the constructed endomorphism.

The character spaces, stability, and intertwiners throughout are the actual
all-affine-algebra predicates. Nonreduced tests are included. No smoothness,
reducedness, characteristic restriction, torsion-free character group,
finite stabilizer, or extra splitting hypothesis is introduced.

## Source and proof route

The target is Milne, *Algebraic Groups* (2017), Theorem 12.30, printed page 241,
with proof on page 242 (one-based PDF pages 257–258), registered source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The coefficient decomposition is the coordinate form of Theorem 12.12,
printed pages 234–235 (PDF pages 250–251). The original passages and official
2017 errata snapshot of 2026-11-02 were read; no listed correction affects
these two theorems.

The implementation works directly over the supplied separable closure,
using coefficientwise subspace descent and linear-functional descent of
intertwiners. It uses finite original coefficient spaces to realize characters
and a minimum-support fixed-vector argument for character stabilizers. It
therefore does not require an explicit finite Galois orbit representation or
an appeal to a categorical semilinear descent equivalence. The supporting
modules' paired Markdown files describe their individual constructions.
