# Exact cuspidal contragredient reduction to archimedean model forms

This module proves the conditional statement
`CuspidalArchimedeanModelPairingReductionStatement`. Its conclusion is
the unchanged Library
`CuspidalTransposeInverseContragredientStatement`, with the number-field
universe free and all its actual cuspidal realization quantifiers retained.

The sole retained premise is
`CuspidalArchimedeanModelPairingStatement`. At each real and complex place
of every actual cuspidal realization, it asks for a nonzero complex
bilinear inverse-transpose form on the chosen actual local source model
`T.placeDensityModels`. These sources are actual irreducible admissible
subspaces with genuine real or complex GK actions and all the hypotheses
of the proved density theorem. The compact twist is the actual matrix
inverse transpose. The Lie twist is negative ordinary transpose on the
whole underlying real matrix Lie algebra, followed by complexification.
The premise does not assume any global pairing, global tensor
factorization, or identification with contragredient functionals.

The implemented proof discharges the global assembly obligations:

1. Choose a nonzero irreducible admissible actual finite factor of `T`.
   The proved finite adelic construction supplies its nonzero transpose
   form using published local nonarchimedean GK and actual Flath
   factorization. Spherical reference normalization and the actual
   restricted-tensor form construction are implemented in its imports.
2. Every chosen actual archimedean source occurs nontrivially in the
   finite-factor multiplicity space: contract its inclusion through the
   proved finite tensor evaluation equivalence. The jointly irreducible
   commuting family of actual place actions and source density then
   assemble the supplied local forms into a nonzero form on that
   multiplicity space. This is the proved finite-family induction,
   including residual irreducibility and persistence of the remaining
   local components under contraction.
3. Direct comparisons of the local and global involutions, compact
   generation by individual places, and the genuine Lie place sum give
   full archimedean transpose identities. Tensor with the finite form
   and transport by actual evaluation to get precisely
   `T.realization.IsTransposeInvariantPairing B` and `B ≠ 0`.
4. The imported nonzero intrinsic-form reduction transports that form
   to the actual cuspidal transpose realization, applies the proved
   cuspidal invariant-pairing criterion, and gives every vector exactly
   its prescribed `dualFunction` cusp form. Thus its conclusion is the
   exact target, including the contragredient relation and all actual
   dual cusp functions.

The provenance is internal composition of these completed constructions
and published proofs. Local archimedean form existence remains an
explicit input here; `cuspidalArchimedeanModelPairing_of_localGK`
(module `CuspidalLocalGKTransposePairingReduction`) derives it from
`Archimedean.ArchimedeanTransposePairingStatement`, which the Library
proves (`Archimedean.archimedeanTransposePairing`, module
`TransposePairingProof`). This conditional intermediate does not prove
the unconditional target; the Library proves it as
`cuspidalTransposeInverseContragredient` (module
`CuspidalTransposeInverseContragredientProof`).
