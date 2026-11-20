# Arithmetic transport of the standard spherical double cosets and Haar measure

Let `a : L ≃+* K` be an isomorphism of number fields and `v : FinitePlace K`.
Write `w = finitePlaceEquiv a v`. The results compare the canonical p-adic
models of the completions at `w` and `v`. The number field universes are
independent.

`residueCardinality_finitePlaceEquiv` restricts `finiteCompletionEquiv a v`
to the canonical valuation integer rings. `finiteCompletionEquiv_integral`
preserves and reflects membership in the completed integers, which
`mem_localIntegers_iff_canonical` identifies with the canonical valuation
integers. `IsLocalRing.ResidueField.mapEquiv` induces an equivalence of the
residue fields, and `Nat.card_congr` gives equality of their cardinalities.

`localEquiv_mem_standardDoubleCoset_iff` compares membership in the two
spherical double cosets at every index `i : Fin (r + 2)`. First, the canonical
uniformizers both have completion valuation `WithZero.exp (-1)` by
`discreteValuation_eq_of_vle` and `uniformizerUnit_zpow_value`. The completion
isomorphism preserves that valuation, so the ratio of the image of the source
uniformizer to the target uniformizer has valuation one. The diagonal matrix
with this ratio in the first `i` slots and one elsewhere belongs to the target
spherical subgroup by `diagonalUnits_mem`. Its product with the target standard
diagonal is the image of the source standard diagonal, as checked entrywise.
Thus the latter matrix lies in the target standard double coset. The already
proved integral subgroup comparison preserves and reflects spherical subgroup
membership. Applying the local group isomorphism and its inverse to the two
subgroup factors then gives the double-coset membership equivalence.

`measurePreserving_localEquiv_sphericalHaar` proves that the same local group
isomorphism pushes the spherical Haar measure forward to the spherical Haar
measure at the corresponding completion. `localGL_topology_eq` gives
continuity of the isomorphism and its inverse for both canonical p-adic
topologies. With their Borel spaces, the proof applies
`RankinSelberg.FieldTransport.normalizedCompactOpenHaar_map` to the two spherical
compact open subgroups. The membership equivalence from
`localEquiv_mem_sphericalSubgroup_iff` identifies the preimage of the target
subgroup with the source subgroup, so the pushforward has the same mass-one
normalization.

This is an internal compatibility of `AdelicGLTransport.localEquiv` with the
actual residue fields, double cosets, and Haar measures used by the standard
Hecke operators. It supplies the local arithmetic comparisons for Task 7880.
