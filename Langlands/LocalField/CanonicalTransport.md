# Arithmetic transport under a p-adic algebra equivalence

Author: Worker 20. This is an internal construction on the published canonical
local-field arithmetic objects. All declarations lie in
`Langlands.PadicField.CanonicalTransport`.

## Inputs and actual residue map

Fix a prime `p`, finite p-adic fields `F` and `E` in independent universes,
and an actual `Padic p`-algebra equivalence `e : F.Carrier ≃ₐ[Padic p] E.Carrier`.
The arithmetic objects use `F.canonicalTopologicalData` and
`E.canonicalTopologicalData`. No chosen residue-field equivalence,
valuation-preservation certificate, or cardinality equality is supplied.

`residueEquiv F E e` is a ring equivalence between those exact residue fields.
Its forward homomorphism is the published `extensionResidueMap F E e.toAlgHom`;
its inverse is `extensionResidueMap E F e.symm.toAlgHom`. The two inverse laws
rewrite a composite residue map as the residue map of the composite field
homomorphism, cancel `e` with its inverse, and use the residue-map identity law.
This reuses the published integer-ring restriction and local residue functor.
It does not construct another quotient model.

`residueEquiv_residue` records its action on every actual integer-ring element:
reduce after applying the published `extensionIntegerMap`, or reduce first and
apply `residueEquiv`; the results agree by definition.

`residueCardinality_eq F E e` gives `q_E = q_F` by `Nat.card_congr` applied to
this equivalence. The equivalence argument is retained explicitly even though
it does not occur in the equality's displayed sides.

## Normalization, order and valuation

`normalizedAbs_map` proves preservation of the residue-cardinality normalized
absolute value at every field element. It uses the existing formula expressing
that value as the canonical spectral norm raised to the degree over `Padic p`.
The published `canonicalNorm_map` preserves the norm, and the actual algebra
equivalence's underlying linear equivalence identifies the two degrees.

`ord_map` then proves `ord_E(e x) = ord_F(x)`. At zero both integer orders have
the specified value zero. Away from zero, rewrite the normalized absolute
values as `q ^ (-ord)`, use `residueCardinality_eq`, and use `q_F > 1` to cancel
integer powers and then their negative signs.

`discreteValuation_map` proves equality of the two actual `WithZero
(Multiplicative ℤ)`-valued discrete valuations. The proof treats zero separately;
away from zero, `ord_map` identifies the valuation logarithms, and
`WithZero.exp_log` recovers the values. Thus the convention for order at zero
has not been used to infer a false valuation equality.

## Derived provenance and exact dependencies

This module asserts no new theorem attributed to external literature. It
composes already published constructions and proves their intrinsic
compatibility under an invertible field map:

- `Langlands/Weil/Local/ExtensionResidue.lean`: `canonicalNorm_map`,
  `extensionIntegerMap`, `extensionResidueMap`, `extensionResidueMap_comp`, and
  `extensionResidueMap_id`. Their paired documentation describes construction
  from the canonical spectral norm and the actual local residue functor.
- `Langlands/LocalField/Normalization/Definitions.lean`: `ResidueField`,
  `residueCardinality`, `discreteValuation`, `ord`, and `normalizedAbs`.
- `Langlands/LocalField/Normalization/Proof.lean`:
  `normalizedAbs_eq_canonicalNorm_pow_degree`, `normalizedAbs_of_ne_zero`,
  `residueCardinality_gt_one`, and `ord_zero`.
- Pinned Mathlib: `Nat.card_congr`, `LinearEquiv.finrank_eq`,
  `zpow_right_injective₀`, and `WithZero.exp_log`.

The imported Library pairs retain their source provenance and authorship.
These internal proofs add no source hypotheses or existence axioms.

## Scope

The result concerns the specified canonical topological data and an actual
algebra equivalence over the same p-adic base. It does not assert that arbitrary
field embeddings preserve normalized order, that distinct choices of closure
embedding coincide, or that chosen uniformizer elements coincide. It constructs
no reciprocity map or epsilon system. Conductor and factor transport can consume
the proved valuation and cardinality identities in later contributions.
