# Transport of actual opposite continuations by conjugation and compact change

The forward and reverse constructions use the conjugation squares for the
actual standard integrals from `DynamicOppositeConjugationScalarProof`.
They reuse the internal compact equivalences, full-domain identities and
operator equalities from that proof through Lean's `open private` command.
The continuation construction is the internal `transportContinuation` of
`DynamicOppositeConjugationScalarTransport`.

`exists_conjugatedChangedCompact_canonicalScalar` pulls back the given
convergence and irreducibility opens through the group-scheme parameter
isomorphism. It uses `conditionalDynamicOppositeConjugationScalar` to
transport the scalar. `forwardContinuationChangeCompact`,
`reverseContinuationChangeCompact` and
`conditionalCanonicalRationalScalar_changeCompact` then give the actual
continuations and scalar at the new compact. The comparison retains the
positive product of the specified Haar scales. These are derived steps
from Waldspurger IV.3(3), printed p. 286, with compact normalization as
in I.1, printed pp. 240–241 (source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).
