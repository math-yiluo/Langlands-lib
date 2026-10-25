# Universe-zero finite reciprocity targets

This module provides two transparent, closed `Prop` abbreviations in
`Langlands.LocalClassField.NYLL`. It imports the existing
[`FiniteReciprocityStatement`](../FiniteReciprocityStatement.lean) and changes
only the universe arguments at which its propositions are instantiated.

| New declaration | Definition in `Langlands.LocalClassField` |
| --- | --- |
| `FiniteAbelianReciprocityTypeZeroStatement` | `FiniteAbelianReciprocity.{0, 0}` |
| `FiniteAbelianNormTransferTypeZeroStatement` | `FiniteAbelianNormTransfer.{0, 0, 0}` |

Each abbreviation has unapplied type `Prop`, no universe parameters, and no
outer term parameters. Its value is the indicated host proposition, with every
field carrier in `Type 0`. Unfolding it retains all the host quantifiers,
hypotheses and conclusions. In particular, every prime is quantified; no prime
or field is selected.

## Preserved mathematical content

The reciprocity target quantifies over `F`, `E`, their algebra and scalar-tower
structures, finite dimension, the abelian Galois hypothesis, and every supplied
`TF : F.TopologicalData` and `TE : E.TopologicalData`. It asserts a continuous
multiplicative equivalence from the quotient of `F.Carrierˣ` by the actual range
of `Units.map (Algebra.norm F.Carrier (S := E.Carrier))` to the actual group
`Gal(E.Carrier/F.Carrier)`. The quotient topology comes from `TF.topology`;
the Galois target retains its Krull topology.

For every `a` of order one and every integral `x`, the geometric normalization
is the host congruence
`TE.discreteValuation ((r (QuotientGroup.mk a)).symm x -
x ^ TF.residueCardinality) < 1`.
It concerns the inverse automorphism and applies also to ramified extensions.
The same witness `r` satisfies the host inertia equivalence: an automorphism is
represented by a unit `a` with `TF.ord a = 0` exactly when it acts trivially
modulo the maximal ideal on every integral extension element.

The norm-transfer target retains every algebra, finite-dimension and
scalar-tower assumption on `F`, `E`, `L`, the abelian Galois hypothesis on `L/F`,
and the supplied `TF` and `TE`. Its two quotient equivalences satisfy both host
equations. The norm `Eˣ → Fˣ` corresponds to
`Gal(L/E) → Gal(L/F)` via `restrictScalars`. Scalar inclusion `Fˣ → Eˣ`,
followed by that Galois inclusion, corresponds to the
`Module.finrank F.Carrier E.Carrier` power. Norm and scalar inclusion retain
their distinct directions.

No abbreviation takes a reciprocity map, selected family, normalization
certificate or comparison theorem as a premise. Each preserves the existential
choices of its host proposition. The two propositions do not identify their
respective existential witnesses with each other, assert uniqueness, or assert
simultaneous coherence over every tower.

## Provenance and scope

These are internal interface aliases, authored by Worker 159, derived solely by
specializing the existing host declarations. The choice of names follows unit
3(a) of the project's
[NYLL source audit](../../../../notes/reuse/nyll-finite-local-reciprocity-audit.md)
and section 7 of the
[port-feasibility report](../../../../notes/reuse/nyll-port-feasibility.md).
There is no copied NYLL implementation in this module and no NYLL import.

The underlying mathematical source is Jean-Pierre Serre, *Local Fields* (1979),
registered as `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 159 read XIII.4, printed pages 196–198 / PDF pages 201–203:
Proposition 8 and its corollary give the finite norm-quotient reciprocity
isomorphism; Proposition 10 gives the norm and transfer diagrams; Proposition
12 gives restriction; Proposition 13 and its corollary give unramified
Frobenius normalization and the valuation-unit image in inertia.
The host [companion Markdown](../FiniteReciprocityStatement.md) explains the
derived congruence formulation, topology and abelian degree-power formulation.
It uses the geometric convention, obtained by inverting Serre's arithmetic
reciprocity values. This module inherits that convention without altering it.
The aliases and universe specialization are internal formalization choices,
not new statements attributed verbatim to Serre.

These targets are intermediate goals for the universe-zero construction.
They do not establish the host propositions at independent arbitrary universes
`u`, `v`, `w`. Transport to those universes, comparison for arbitrary supplied
topological data, and the reciprocity proofs remain separate obligations.
The module supplies no Artin map, adapter, theorem proof, class-formation result
or Weil-group system. The imported host Lean/Markdown pair is unchanged.
