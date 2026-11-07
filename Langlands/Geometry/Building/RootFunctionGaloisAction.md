# Actual coefficient transport of root-function families and filtrations

Let `k` and `K` be fields in an arbitrary common universe, with a supplied
`k`-algebra structure on `K`. Supply a commutative group scheme `T` and a group
scheme `G` over `k`. Write `T_K` and `G_K` for their actual base changes. No
splitness, reductivity, smoothness, affineness, finiteness or Galois-extension
hypothesis is used in this module.

`RootFunctionFamily.galoisAction` is a group homomorphism from the actual group
`K ≃ₐ[k] K` to permutations of the existing root-function families for `T_K` and
`G_K`. Its value at `sigma` sends a family `phi` to the family whose value at a
character `a` and rational point `g` is

```
phi (sigma inverse · a) (rationalConjugate sigma inverse g).
```

The character map is the existing integral character-lattice representation;
the point map is the existing `rationalConjugate` on the existing rational-point
carrier. This construction leaves the `WithTop` real value unchanged. The inverse
convention makes simultaneous transport of the family, character and point
preserve values exactly, as `galoisAction_apply_conjugate` proves. The inverse
permutation is given by transport in the opposite direction. The inverse,
identity and multiplication laws follow from the two existing representation
laws, with reversal of order on taking the inverse of a product.

`galoisAction_vadd` intertwines the existing translation of families by real
cocharacters with the actual real coefficient action `galoisCocharacterAction`.
The proof is pointwise and uses the inverse-character evaluation formula from
`GaloisTranslationAction`. Consequently `galoisAction_equipollent` preserves
equipollence: a witness vector transports by that same real action. These
assertions apply to arbitrary families, without valuation or normalization
assumptions.

For any supplied descended map `i : T.toGrp ⟶ G`,
`rationalConjugate_mem_rootFiltration_iff` proves exact covariance of the actual
`rootFiltration` sets for every character, every real depth, every family and
every rational point. Membership is the conjunction of membership in the actual
intrinsic root subgroup and the valuation inequality. The first part is exactly
`RelativeRoot.rationalConjugate_mem_subgroup_iff` from
`RootSubgroupGaloisTransport`; the second follows from simultaneous value
invariance. `image_rootFiltration_galoisAction` upgrades this equivalence to an
exact image equality under the existing coefficient-conjugation map. Its reverse
inclusion uses the explicit inverse coefficient conjugate as a preimage and the
coefficient multiplication identities.

This is an internal derivation from the imported actual character, cocharacter,
point and root-subgroup transports, and the definitions of families,
equipollence and root filtrations. It introduces no external literature
assertion. It constructs the full family action and all-depth filtration
transport. It does not construct a coefficient-stable valuation class or an
apartment, establish compatibility with the normalizer action, or supply a
metric, special point, supplied-model stabilizer or descent comparison. The full
`BuildingComparisonStatement` remains open.
