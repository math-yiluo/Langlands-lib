# Finite-family equivalence and geometric normalization

This internal construction applies the actual finite-family reconstruction
without asserting arithmetic existence. For any field with any supplied
topology, `finiteFamilyOfHom_compatible` proves that the actual restrictions
of a continuous homomorphism satisfy every finite restriction identity.
It applies the composition identity for actual restrictions pointwise.

For every perfect field `K : Type u`, `finiteFamilyEquiv` identifies continuous
homomorphisms from its units to its actual absolute-Galois closed-commutator
quotient with the subtype of continuous finite Artin families satisfying
actual restriction compatibility. The forward map takes actual finite
restrictions, and its inverse is `FiniteArtinReconstruction.reconstruct`.
The inverse identities use recovery of every supplied finite component and
separation of maps by their finite restrictions. No topology is replaced.

`reconstruct_geometric` works for every prime, arbitrary-universe p-adic
field `F`, and supplied base datum `T`. It takes a supplied finite Artin
system certificate and the exact geometric residue congruence for every
actual finite abelian extension `L`, every supplied datum `S` on that
extension, every unit `b` with `T.ord b = 1`, and every integral `x` in `L`.
It proves the existing `GeometricProfiniteReciprocityRelation F T` for the
reconstructed map. The norm-residue component is
`FiniteArtinReconstruction.reconstruct_normResidue`; finite component
recovery makes its geometric normalization literally the supplied residue
congruence. The inverse automorphism and exponent `T.residueCardinality`
are preserved exactly. Characteristic zero, hence perfectness, is derived
from the actual finite extension of `Padic p`.

Provenance is internal: this module derives an equivalence and preservation
of the already-defined geometric relation from the actual restriction and
reconstruction lemmas. It adds no literature assertion or arithmetic
witness. The unconditional finite-system existence and uniqueness theorem
and the final unconditional profinite reciprocity theorem remain required.
