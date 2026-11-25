# Independence of a restricted tensor representation from its reference vectors

## Main theorem

```lean
theorem Langlands.restrictedTensorReferenceIndependence :
    Langlands.RestrictedTensorReferenceIndependenceStatement.{uI, uG, uV}
```

The index, local-group and carrier universes are independent. Let `ρ i` be
admissible complex representations of Hausdorff, locally compact, totally
disconnected groups `G i` with compact open subgroups `H i`. The reference
families `r` and `r'` supply nonzero `H i`-fixed vectors outside `E` and `E'`,
respectively. If the fixed spaces of `ρ i` under `H i` are one-dimensional at
all but finitely many indices, the two `productRepresentation` constructions
are equivalent as representations of `RestrictedGroup G H`.

## Proof

- `RestrictedTensor.exists_reference_smul` places both reference vectors in
  `fixedVectors (ρ i) (H i)` at an index outside `E ∪ E'` where that subspace
  has dimension one. Mathlib's `finrank_eq_one_iff_of_nonzero'` expresses the
  second vector as `c • r.vector i hi`. Its nonvanishing gives `c ≠ 0`.
  The other branch supplies `1`.
- Choose the scalars `c i`. Each `LinearEquiv.smulOfNeZero` acts on `V i` by
  multiplication by `c i`, which commutes with `ρ i g` by linearity. The
  cofinite fixed-line condition and the finiteness of `E` and `E'` give
  `f i (r.family i) = r'.family i` at all but finitely many indices, using
  `ReferenceVectors.family_of_not_mem`.
- `RestrictedTensor.congr` assembles these maps into a linear equivalence of
  the restricted tensor products. `RestrictedTensor.map_intertwines` gives
  equivariance for the restricted-product action, and
  `Representation.Equiv.mk` bundles the resulting equivalence.

## Provenance

D. Flath, *Decomposition of representations into tensor products*, in
*Automorphic Forms, Representations and L-functions*, Proc. Sympos. Pure
Math. 33, Part 1 (1979), section 2, printed p. 181 (one-based PDF p. 177).
Example 2 asserts independence of the nonzero choices in the fixed lines.
The preceding assertion (3) gives the isomorphism for reference vectors
lying on the same lines at almost all indices. The Lean proof implements that
comparison by rescaling the local factors and using the Library's restricted
tensor maps for the group actions.

The registered source is `flath-1979-tensor-products`, with volume SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
