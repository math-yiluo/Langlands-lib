# Same-carrier p-adic realization

This module realizes a supplied characteristic-zero nonarchimedean local field
`T : LocalFieldData F` as a finite extension of `Padic p` on the **same** field
`F`. The prime `p` is supplied with `[Fact p.Prime]` and
`[CharP T.ResidueField p]`, so it is the characteristic of the actual residue
field `T.ResidueField` of the supplied valuation. The theorem
`residueCharacteristic_prime` proves that `ringChar T.ResidueField` is prime,
because that residue field is finite; a consumer can therefore take
`p := ringChar T.ResidueField` with `ringChar.charP`.

## Source

André Weil, *Basic Number Theory*, second edition, Springer, 1973 (source
`weil-1973-basic-number-theory`), Chapter I, restricted to commutative fields of
characteristic zero:

- §3, Theorem 5(b) and its proof, pp. 11–12 (PDF pp. 28–29): a non-discrete
  locally compact field `K` of characteristic zero contains the closure of the
  prime field `ℚ`, which is isomorphic to a completion `ℚ_v`; in the
  nonarchimedean case `v` is the prime `p` with `mod_K(p · 1_K) < 1`, and `K`
  is finite-dimensional over `ℚ_p`.
- §2, Theorem 3, Corollaries 1–2, p. 6 (PDF p. 23): a finite-dimensional vector
  space over a non-discrete locally compact field has a unique structure of
  topological vector space, and a locally compact topological vector space over
  such a field is finite-dimensional. Corollary 2 is the finiteness step in the
  proof of Theorem 5(b); Corollary 1 is the uniqueness of the vector-space
  topology.
- §4, Theorem 6, pp. 12–13 (PDF pp. 29–30): for such a `p`-field, the residue
  field `R/P` is finite of characteristic `p`, since `p · 1_K ∈ P`. This
  identifies the prime of Theorem 5(b) with the residue characteristic, which
  is how this module chooses `p`.

Weil compares the module `mod_K` with the absolute value `|·|_p` on `ℚ`. The
Lean construction compares valuation rings instead, and replaces Weil's
closure of `ℚ` in `K` by the extension of a continuous map from the completion.

## Lean construction

The section `RationalValuation` works with an ambient `ValuativeRel F` and
`CharP 𝓀[F] p`. Integer casts are integral, and an integer cast has value
strictly less than one exactly when its residue vanishes, that is, when `p`
divides it. A rational number in lowest terms is integral exactly when `p`
does not divide its denominator: if `p` divides the denominator then it does
not divide the numerator, whose value is then one
(`valuation_ratCast_le_one_iff`). This is Mathlib's criterion for the rational
`p`-adic valuation, so the restriction of the supplied valuation to `ℚ` is
equivalent to `Rat.padicValuation p` (`valuation_ratCast_isEquiv`); the two
valuations need not be equal.

The section `PadicEmbedding` adds the topology and `IsNonarchimedeanLocalField F`.
The inclusion of `ℚ`, with its `p`-adic valued structure, is continuous at
zero: the value group has rank at most one, hence is archimedean, and the
value of `p` is less than one, so the values of the powers of `p` are cofinal
toward zero. With the
uniform structure of the additive topological group `F`, which is complete
and Hausdorff, the inclusion extends from the completion to the ring
homomorphism `padicEmbedding F p : Padic p →+* F` (`continuous_padicEmbedding`,
`padicEmbedding_ratCast`). The preimage of the supplied valuation ring and the
`p`-adic valuation ring are clopen in `Padic p`, and their membership
predicates agree on the dense subset `ℚ`. The set where they agree is closed,
so they agree everywhere. This gives `padicEmbedding_isEquiv`: the supplied
valuation restricted along `padicEmbedding F p` is equivalent to
`Padic.mulValuation`.

`padicAlgebra F p` is the algebra structure of `padicEmbedding F p`. Scalar
multiplication is continuous because multiplication and the embedding are
continuous. Mathlib's `FiniteDimensional.of_locallyCompactSpace` gives finite
dimension over `Padic p`, the counterpart of Weil's §2, Theorem 3,
Corollary 2. `isModuleTopologyOfFiniteDimensional` identifies the supplied
topology with the module topology, the counterpart of Corollary 1.
`isClosedEmbedding_padicEmbedding` proves that the embedding is a closed
topological embedding. Since `Padic p` is a field, the injective linear map
`Padic p → F` has a linear left inverse. That left inverse is continuous for the module
topology, and a continuous map with a continuous left inverse into a Hausdorff
space is a closed embedding.

## The realization

The section `Realization` starts from `T : LocalFieldData F` and installs its
topology, valuative relation and local-field certificate locally.

- `toPadicField T p : PadicField p` is `PadicField.ofField F` with the algebra
  structure `padicAlgebra F p`. `toPadicField_carrier` and `toPadicField_field`
  state that its carrier and field structure are those of `F`, by `rfl`.
- `toPadicTopologicalData T p` is the `PadicField.TopologicalData` whose
  topology, valuative relation and local-field certificate are those of `T`
  (`toPadicTopologicalData_topology`, `toPadicTopologicalData_valuativeRel`,
  `toPadicTopologicalData_localField`). The fields `valuativeExtension` and
  `moduleTopology` are the certificates of the previous section.
- `toPadicTopologicalData_toLocalFieldData` states that
  `(T.toPadicTopologicalData p).toLocalFieldData = T` holds by `rfl`. The map
  `PadicField.TopologicalData.toLocalFieldData` is the forgetful map of
  `Langlands.LocalField.PadicBridge`.
- The algebra map of `T.toPadicField p` extends the inclusion of `ℚ`
  (`algebraMap_toPadicField_ratCast`). It is a closed embedding for the
  supplied topology (`isClosedEmbedding_algebraMap_toPadicField`). The supplied
  valuation restricted along it is equivalent to `Padic.mulValuation`
  (`isEquiv_comap_algebraMap_toPadicField`).

## Relation to other modules

`Langlands.CharZeroLocalField.padicField` and
`Langlands.CharZeroLocalField.topologicalData`, in
`Langlands.LocalField.CharZeroPadicRealization`, give the same kind of
realization for a field with ambient instances, at the fixed prime
`ringChar 𝓀[F]`. The present module starts from `LocalFieldData` and takes any
prime `p` with `CharP T.ResidueField p`. Its algebra map is then a ring
homomorphism from `Padic p` itself, with no transport along the equality
`ringChar T.ResidueField = p`.

This module only builds the realization. It does not prove uniqueness of p-adic
realizations, compare scalar maps in towers of extensions, or treat local
fields of positive characteristic.
