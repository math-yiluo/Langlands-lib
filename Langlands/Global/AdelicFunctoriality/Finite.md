# Arithmetic transport at finite places

This module constructs transport of actual finite places, completed fields,
integral subrings and finite adeles along a number-field isomorphism
`e : K ≃+* L`. The fields have independent universes. All constructions use
Mathlib's rings of integers and its genuine adic completions and restricted
products.

`finitePlaceEquiv e` pulls back nonzero prime ideals along
`RingOfIntegers.mapRingEquiv e`, so it runs from the finite places of `L`
to those of `K`. Prime powers commute with transport. Comparing membership
in every prime power proves equality of the normalized adic valuations on
the rings of integers; expressing field elements as fractions proves
`finitePlaceEquiv_valuation` on the fields.

`finiteCompletionEquiv e p` extends the field isomorphism to the actual
adic completions at `p` and its pullback. The private uniform-continuity
proof uses the valuation-ball neighborhood bases and the proved valuation
equality; it assumes no topological arithmetic map. Both completion maps
are continuous, and `finiteCompletionHomeomorph` bundles the same
equivalence as a homeomorphism. The map agrees with `e` on the dense field
subspace. The valuations on the completions are continuous into the
integer value group with its zero topology, so density extends the valuation
equality to all completed elements. Consequently the map preserves the
valuation subrings in both directions (`finiteCompletionEquiv_integral`).

`finiteAdeleMap e` uses `RestrictedProduct.mapAlongRingHom`, reindexing
with `finitePlaceEquiv e` and applying the proved completion maps.
The equivalence of index sets preserves the cofinite filter, and integrality
holds at every corresponding place. Thus the restricted-product condition
is proved for the actual finite adele ring; it is not an unexplained field
of an interface. Mathlib's restricted-product continuity lemma proves
continuity in its restricted-product topology.

Identity and composition are first proved on each completed field by density
of that field's diagonal map, then coordinatewise on finite adeles.
They produce `finiteAdeleEquiv e` and `finiteAdeleHomeomorph e`.
The `_apply` and `_diagonal` lemmas give the exact coordinate and diagonal
formulas, and `_refl` and `_trans` give the intrinsic functorial laws.
The proof does not require a strong-approximation theorem for finite adeles.

The arithmetic definitions follow Andre Weil, *Basic Number Theory*, second
edition (1973), Chapter III section 1, Definitions 2-4, printed pp. 43-45
(PDF pp. 60-62), and Chapter IV section 1, Definition 1, printed pp. 59-60
(PDF pp. 76-77). Registered source `weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
The ideal-membership proof implements isomorphism invariance directly using
pinned Mathlib's genuine rings of integers, height-one primes and adic
valuations. No field-extension norm is defined or assumed here.

The only formal dependencies are the pinned Mathlib interfaces, including
`HeightOneSpectrum.comap`, `intValuation_le_pow_iff_mem`, fraction-ring
surjectivity, `WithVal.congr`, completion ring maps, and restricted-product
transport. No other project artifact is imported. Combining this group
with infinite adeles, passing to units and principal quotients, and constructing
finite-extension norms remain separate required parts of the assigned task.
