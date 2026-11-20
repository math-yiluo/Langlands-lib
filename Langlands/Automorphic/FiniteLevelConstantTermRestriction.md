# Finite-level restriction of maximal block constant terms

Harish-Chandra, *Automorphic forms on semisimple Lie groups* (1968), Chapter I,
§6, printed pp. 19–20, describes the induction using the restrictions of
constant terms to the Levis of maximal cuspidal parabolics and the vanishing
of all constant terms on the cuspidal subspace (PDF pp. 29–30 of the
registered edition). The construction here gives the adelic restriction
and its kernel for the concrete maximal block constant terms of $\mathrm{GL}_n$.
It uses the Library's unnormalized constant term, computed using the
probability Haar measure on the compact matrix quotient.

For each ordered pair of positive block sizes summing to $n$, put the
corresponding adelic matrices on the diagonal. The map `blockConstantTermAt`
takes the constant term after this embedding and one fixed right translation
in the finite adelic factor. `restrictMultiplicityToConstantTerms` composes
that map with each compact-equivariant linear map in the given multiplicity
space. Its coordinates are indexed by the ordered block cuts and a finite
set of finite adelic translations.

The projection of the standard adelic compact group to the finite adelic
factor is compact, so finitely many cosets modulo the open level cover it.
For any adelic argument, an Iwasawa factorization expresses it as an upper
triangular element times a standard compact element. Relative to a chosen cut,
the upper triangular element is a block unipotent matrix times a block
diagonal matrix. In block coordinates its diagonal blocks are invertible by
the block triangular determinant formula, and the unipotent coordinate is
the upper off-diagonal block multiplied on the right by the inverse of the
second diagonal block.

Translation invariance of Haar measure removes the left block unipotent
matrix from the constant term. On the right, level invariance removes the
level element, and compact equivariance transfers the infinite compact
component to the vector in the source representation. This recovers each
constant term value from the joint restriction. The reverse kernel inclusion
follows by evaluating the vanishing constant terms at the restricted
arguments. The proof applies to every open level and to the algebraic
compact source in the published Harish-Chandra finiteness statement.
