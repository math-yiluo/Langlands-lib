# Symmetrizing a pairing with locally finite asymmetry

Author: Worker 143. Module `Langlands.LinearAlgebra.LocallyFiniteHermitian`, namespace `Langlands.LinearAlgebra`.

This is derived internal linear algebra supporting the first assertion of Renard IV.2.1, Remark 1. It supplies the symmetrization that is needed after identifying a representation with its hermitian contragredient. The exact source target is documented in `Langlands/Representation/Unitary/HermitianRepresentationStatements.md`. The argument below is an implementation proof, rather than a claim that the source spells out these steps.

## Result and conventions

`exists_hermitian_of_locallyFinite_asymmetry` takes a complex sesquilinear form `B`, conjugate linear in its first variable and linear in its second, with left nondegeneracy, and an endomorphism `T` such that

`B(T x, y) = conj(B(y, x))`.

It assumes `T` is locally finite, meaning that each vector lies in a finite dimensional invariant subspace, as defined in `LocallyFiniteJordan`. It constructs a left nondegenerate hermitian form `H`. Every linear endomorphism commuting with `T` and preserving `B` also preserves `H`. There is no finite dimensionality hypothesis on the whole space, no positivity assertion, and no group in this algebraic helper.

## Implemented construction

Write `B*(x,y) = conj(B(y,x))`. Applying the asymmetry identity twice proves `B(Tx,Ty) = B(x,y)`.

For a locally finite complex endomorphism, its maximal generalized eigenspaces span the space: restrict to a finite dimensional invariant subspace containing a given vector, apply the algebraically closed finite dimensional decomposition there, and map it into the ambient space. Independence of the generalized eigenspaces then gives a direct sum `V = N ⊕ C`, where `N` is the maximal generalized −1 eigenspace and `C` is the sum of all the other maximal generalized eigenspaces.

Put `A = T + 1`. The map `A` is surjective on `C`. To verify this on a generalized eigenspace for `b ≠ -1`, intersect that eigenspace with a finite dimensional invariant subspace containing the supplied vector. The restriction of `A` to this intersection is injective, since a vector in its kernel belongs to both generalized eigenspaces for `b` and −1. Finite dimension makes the restriction surjective. Taking sums proves surjectivity on `C`.

The asymmetry identity implies

`B(A^n x, T^n y) = B(x, A^n y)`.

If `x ∈ N`, some `A^n` kills `x`, whereas every vector of `C` has an `A^n` preimage in `C`. This proves `B(N,C) = 0`. The relation `B(Tx,y) = conj(B(y,x))` and preservation of `N` by `T` give `B(C,N) = 0` as well.

Let `P` and `Q` be the projections onto `N` and `C` respectively. The implemented form is

`H(x,y) = B(Qx,Qy) + conj(B(Qy,Qx)) + i (B(Px,Py) - conj(B(Py,Px)))`.

Conjugation shows directly that this is hermitian. If `H(x,-)` vanishes, testing against `Py` gives `B((1-T)Px,Py) = 0`. Orthogonality extends this to all second arguments; nondegeneracy of `B` gives `(1-T)Px = 0`. The generalized −1 and 1 eigenspaces are disjoint, so `Px = 0`. Testing against `Qy` similarly gives `B((T+1)Qx,Qy) = 0`, hence `(T+1)Qx = 0`. This places `Qx` in both `N` and `C`, so `Qx = 0`. The projection decomposition gives `x = 0`.

Every endomorphism commuting with `T` preserves both `N` and `C`. The projection decomposition therefore shows that it commutes with `P` and `Q`. Substituting into the displayed formula proves the last invariance clause for every such endomorphism that preserves `B`.
