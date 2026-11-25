# Flath's Example 2

## Main theorem

```lean
theorem Langlands.flathRestrictedTensor :
    Langlands.FlathRestrictedTensorStatement.{uI, uG, uV, uW}
```

The four universes belong to the index type, the local groups, and the two
families of representation carriers in the uniqueness clause. Lean proves
the conjunction by supplying four imported theorems in the order of the
published proposition. [Target statement](RestrictedTensorStatement.md)

1. `restrictedTensorAdmissibility` combines smoothness with a finite-stage
   bound on the fixed vectors of each open subgroup.
   [Admissibility proof](RestrictedTensorAdmissibilityProof.md)
2. `restrictedTensorIrreducibility` uses irreducibility of finite stages
   to pass from local to global irreducibility. For the converse it uses
   the map induced by a quotient at one index.
   [Irreducibility proof](RestrictedTensorIrreducibilityProof.md)
3. `restrictedTensorReferenceIndependence` rescales the reference vectors
   on their common fixed lines and applies the induced equivariant linear
   equivalence of restricted tensors.
   [Reference independence proof](RestrictedTensorReferenceIndependenceProof.md)
4. `restrictedTensorFactorUniqueness` restricts a global equivalence to
   each local group, separates its local factor, and cancels the trivial
   multiplicity spaces.
   [Factor uniqueness proof](RestrictedTensorUniquenessProof.md)

## Provenance

The first three clauses come from Section 2, Example 2, of D. Flath's
*Decomposition of representations into tensor products* (1979), printed
p. 181 (one-based PDF p. 177). The preceding assertion (3) explains
equivalence when the reference vectors span the same lines almost
everywhere. The fourth clause applies the isotypic restriction argument
at the end of the proof of Theorem 1, printed p. 180 (PDF p. 176), to the
constructed tensors. This gives the uniqueness conclusion of Theorem 2,
printed p. 181 (PDF p. 177), for those tensors.

The registered source `flath-1979-tensor-products` is the Corvallis Part I
volume with SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
