# Finite abelian local reciprocity, norm, transfer and restriction: proof

The module `Langlands.ClassFieldTheory.Local.FiniteReciprocityProof` proves the
published proposition
`Langlands.LocalClassField.FiniteAbelianReciprocityTheorems.{u, v, w}` with the
theorem

```lean
theorem Langlands.LocalClassField.finiteAbelianReciprocityTheorems :
    FiniteAbelianReciprocityTheorems.{u, v, w}
```

Its type is exactly the target, with independent universe parameters `u`, `v`,
`w`. The target is defined in
[`FiniteReciprocityStatement`](FiniteReciprocityStatement.lean), which the module
imports by its Lean name. The module changes neither that statement nor anything
it imports. Its import closure contains no module under `Langlands/NYLL/`.

## What is proved

The target is the conjunction of three propositions:

- `FiniteAbelianReciprocity.{u, v}`: for every finite abelian extension `E/F` of
  p-adic fields given as separate fields, and arbitrary supplied topological data
  `TF` and `TE`, a continuous isomorphism from the actual norm quotient of
  `F.Carrierˣ` onto `Gal(E/F)` with the geometric residue clause and the
  unit/inertia clause;
- `FiniteAbelianNormTransfer.{u, v, w}`: for every finite abelian tower
  `F ⊆ E ⊆ L` and arbitrary supplied `TF` and `TE`, isomorphisms for `L/F` and
  `L/E` that turn the norm `Eˣ → Fˣ` into the Galois inclusion and the scalar
  inclusion `Fˣ → Eˣ` into the `[E:F]`-th power map;
- `FiniteAbelianRestriction.{u, v, w}`: for every such tower and arbitrary
  supplied `TF`, isomorphisms for `E/F` and `L/F` compatible with
  `AlgEquiv.restrictNormalHom`.

[`FiniteReciprocityStatement.md`](FiniteReciprocityStatement.md) explains these
clauses in full.

## Proof

Each conjunct is the published universe transport applied to the universe-zero
proof of the same proposition:

| Conjunct | Universe-zero proof | Published transport |
| --- | --- | --- |
| `FiniteAbelianReciprocity.{u, v}` | `UniverseZero.finiteAbelianReciprocityTypeZero` ([`TypeZeroReciprocityProof`](UniverseZero/TypeZeroReciprocityProof.lean)) | `UniverseZero.finiteAbelianReciprocityUniverseTransport` |
| `FiniteAbelianNormTransfer.{u, v, w}` | `UniverseZero.finiteAbelianNormTransferTypeZero` ([`TypeZeroNormTransferProof`](UniverseZero/TypeZeroNormTransferProof.lean)) | `UniverseZero.finiteAbelianNormTransferUniverseTransport` |
| `FiniteAbelianRestriction.{u, v, w}` | `UniverseZero.finiteAbelianRestrictionTypeZero` ([`TypeZeroRestrictionProof`](UniverseZero/TypeZeroRestrictionProof.lean)) | `UniverseZero.finiteAbelianRestrictionUniverseTransport` |

All names are in `Langlands.LocalClassField`. Each transport theorem proves that
the universe-zero alias in
[`TypeZeroStatement`](UniverseZero/TypeZeroStatement.lean) implies the corresponding conjunct
at arbitrary independent universes
([`UniverseTransportStatement`](UniverseZero/UniverseTransportStatement.lean)). The
transports are in the published modules `ReciprocityUniverseTransportProof`,
`NormTransferUniverseTransportProof` and `RestrictionUniverseTransportProof`
under `Langlands/ClassFieldTheory/Local/UniverseZero/`. The theorem is the anonymous
constructor of the three resulting proofs.

At universe zero, every reciprocity isomorphism is the quotient of the Library's
geometric finite Artin symbol
`Langlands.LocalClassField.FiniteArtinSystemExistence.geometricSymbol`, through
the supporting theorem `exists_quotientEquiv_geometricSymbol` in
[`FiniteGeometricQuotient`](FiniteGeometricQuotient.lean). The paired Markdown
of each universe-zero module describes its proof.

## Scope and provenance

The theorem proves each conjunct separately. Like the target, it does not claim
that the witnesses of different conjuncts, or of the three conjuncts after
universe transport, are the same choices. It claims no uniqueness and no
coherence over all fields at once. The mathematical source of the target is
Serre, *Local Fields*, XIII.4, Propositions 8, 10, 12 and 13 with their
corollaries (source `serre-1979-local-fields`), in the geometric convention of
the target's Markdown. The proof assembles published Library theorems, through
the Library's own finite Artin symbol. It does not follow Serre's arguments.

The module compiled without errors or warnings (Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection of
`finiteAbelianReciprocityTheorems` reports universe parameters `u`, `v`, `w` and
the axioms `propext`, `Classical.choice` and `Quot.sound` only.
