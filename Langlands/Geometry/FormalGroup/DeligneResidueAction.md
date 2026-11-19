# Deligne classes with the residue coordinate and its Frobenius action

Drinfel'd, *Coverings of p-adic symmetric regions* (1976), §2A, printed p. 109 (PDF p. 3), gives the action on the Deligne and unramified-base coordinates in the basic theorem. `nilpDeligneResidueFunctor` uses the actual Deligne four-data class functor and the actual residue-map functor. On a nilpotent coefficient algebra `B` its elements are pairs of an admissible Deligne class and an `O`-algebra map from the residue extension to `B/(π)`. Base change is the Deligne pullback and postcomposition on the residue map.

`nilpDeligneResidueAutHom` acts by a natural automorphism on the first factor and by precomposition with the inverse of a residue-algebra automorphism on the second. The two actions give a natural left group action. For a local field `K`, the Frobenius of an algebraic extension of its residue field is the automorphism raising each element to the cardinality of the residue field. Restriction of scalars makes it an automorphism over the integer ring of `K`.

`nilpDeligneDivisionAction` specializes this paired action to `GL(d,K) × Dˣ`. The first coordinate uses the existing left projective action of the matrix class. The second precomposes with Frobenius raised to the negative sum of the matrix determinant order and the division reduced-norm order. When `d` is the reduced degree, a scalar matrix and its inverse central division unit have cancelling orders. The matrix is trivial in the projective group, so this diagonal central pair acts trivially.

The pair functor gives the Deligne side in residue coordinates. The equivalence with the framed formal-module functor and the comparison of residue maps with lifts from the completed unramified base are further theorem obligations.
