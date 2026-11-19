# Finite Herbrand functions over nonarchimedean local fields

Worker 845 generalizes the existing `Herbrand.Finite` definitions in place.
All declarations are in `Langlands.Ramification.Local` and use the supplied
integer-ring groups of [`LocalGalois`](../LocalGalois.md). The supplied interface
is `T : LocalField.TopologicalData K₀ L` and a scalar tower `K₀ → K → L`.
The three fields may have independent universes. There is no hypothesis on
any characteristic and no separability requirement for the construction.
In the intended finite Galois local-field application it is Serre's filtration.
As with the published original, groups are also defined for nonnormal
extensions without claiming quotient compatibility in that wider domain.

`lowerRamificationGroupReal T K u` is the integer lower group at `ceil u`.
It retains the original constant full-group extension below −1, agrees with
the natural groups at natural indices, and is inertia at zero. Normality and
decrease follow from the integer construction and monotonicity of ceiling.

Assume `[FiniteDimensional K₀ L]` for the Herbrand functions.
`lowerGroupOrder` is the actual finite subgroup cardinality.
`ramificationCutoff` chooses a bound from proved lower-group termination;
it is not supplied by the caller. `herbrandPhi` uses the published finite
polygon with these orders and this cutoff. Its floor formula, for `u ≥ 0`, is

`φ(u) = (∑ (i < floor u), |G_(i+1)| + (u-floor u)|G_(floor u+1)|) / |G_0|`.

The proved tail formula removes dependence on the cutoff from this expression.
On `u ≤ 0`, φ is the identity. Positivity of every subgroup order proves
strict increase and surjectivity using the existing polygon analysis.
`herbrandOrderIso` packages these facts as an order isomorphism of the real
line, and `herbrandPsi` is its genuine inverse. Both inverse identities,
continuity and strict increase are proved. ψ is also the identity for
nonpositive arguments. `herbrandHalfLineOrderIso` restricts to Serre's domain
`[-1, ∞)`. The extension below −1 is the retained implementation convention.

`upperRamificationGroup T K v` is the real lower group at `ψ(v)`, hence the
integer lower group at `ceil(ψ(v))`. Its −1 and zero values, normality and
decrease follow from the corresponding lower lemmas and inverse identities.
For eventual triviality, apply monotonicity of ψ at `φ(cutoff)` and then the
proved lower cutoff. No arithmetic quotient or tower theorem is used.

## Canonical realizations and the Mathlib-local-field interface

`canonicalUpperRamificationGroup K₀ L hbase K v` uses
`LocalField.canonicalTopologicalData K₀ L hbase`, for a complete, nontrivially
normed ultrametric and locally compact base and a finite extension `L`.
The proof `hbase` identifies norm comparisons with the specified base
valuative relation. This additional base parameter allows the original
`Padic p` norm to be used unchanged.

`localTopologicalData K L` directly constructs the supplied realization for
any `[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]` and any finite field extension `L`.
It installs the already published `LocalGalois.localNormedField K`, its
completeness and ultrametric certificates, and uses
`LocalGalois.localNormedField_le` with valuation compatibility for `hbase`.
Its topology on the base is definitionally the original topology.
`localUpperRamificationGroup K L v` applies the general upper construction
to exactly this realization. Lower groups, Artin/Swan expressions and
Herbrand functions over a Mathlib local base are obtained by supplying
`localTopologicalData K L` to their corresponding general declarations.
For a finite Galois intermediate field of a separable closure take that actual
subfield for `L`, with its inherited field, algebra and finiteness structures.
No local-field realization hypothesis remains to be discharged by the caller.

## Sources, characteristic audit and specialization

Serre, *Local Fields* (1979), IV §3, p.73 (PDF p.80), defines ceiling lower
indexing, the displayed floor formula and the inverse ψ; Proposition 12
states continuity and increase. Upper numbering and its endpoints and
termination are on p.74 (PDF p.81). The lower-group input is IV §1, Lemma 1
and Proposition 1, pp.61–62 (PDF pp.68–69). These original passages were read.
Source `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The registered 2019 author corrections, PDF pp.2–3, were checked; the p.74
correction concerns symbols in the later Lemma 3, not the definitions here.
The finite polygon is the Library's internal implementation of the source
formula, whose equality is proved. The general data packaging is internal.

No finite construction here used characteristic zero implicitly. In particular,
the extended spectral norm, continuity of automorphisms, DVR Noetherianity,
faithfulness, finite automorphism group, cardinality positivity and real polygon
arguments require neither perfectness nor separability. At the absolute level,
the old implicit use of a characteristic-zero algebraic closure as a separable
closure is replaced by a specified `IsSepClosure K Ω`; that change is documented
in the separate absolute unit. No general characteristic-zero instance is added.

In the table the first column has prefix `Langlands.Ramification.Local` and
the second `Langlands.Ramification.Padic`. Substitute `K₀ = Padic p`,
`L = F.Carrier` and `T.toLocalData` for the supplied data.

| General declaration | Existing p-adic specialization |
| --- | --- |
| `lowerRamificationGroupReal T.toLocalData K` | `lowerRamificationGroupReal T K` |
| `lowerGroupOrder T.toLocalData K` | `lowerGroupOrder T K` |
| `ramificationCutoff T.toLocalData K` | `ramificationCutoff T K` |
| `herbrandPhi T.toLocalData K` | `herbrandPhi T K` |
| `herbrandOrderIso T.toLocalData K` | `herbrandOrderIso T K` |
| `herbrandPsi T.toLocalData K` | `herbrandPsi T K` |
| `herbrandHalfLineOrderIso T.toLocalData K` | `herbrandHalfLineOrderIso T K` |
| `upperRamificationGroup T.toLocalData K` | `upperRamificationGroup T K` |
| `canonicalUpperRamificationGroup (Padic p) F.Carrier hbase K` | `canonicalUpperRamificationGroup F K` |

Here the p-adic `hbase` is the norm/valuation comparison used by
`PadicField.canonicalTopologicalData`; its proof is irrelevant to the value.
Each elementary lemma specializes with the same leaf name. The table records
definitional equality of the full constructions, not an added comparison
theorem. Composite p-adic definitions preserve their original outer expression
for existing explicit-unfold proofs; p-adic construction lemmas apply the
corresponding general lemmas with exactly the same original statement text.
`localTopologicalData` and `localUpperRamificationGroup` are conveniences for
the case `K₀ = K`; the base-parameterized definition is the one used by the
legacy p-adic layer to retain its original spectral base norm.

Development check `f3157c00-82eb-42ce-a97b-94895e1ec726` compiled all complete
unapplied public-declaration `rfl` checks against private legacy copies, a
Laurent-series finite-extension usage diagnostic with no characteristic-zero
assumption, and the unchanged `AbsoluteProof`, `WeilInertiaProof`,
`SubextensionProof`, `ConvexityProof`, `WeilRestrictionProof` and `WeilBreakProof`
consumers with zero errors or warnings. The Laurent diagnostic constructs the
groups and applies the zero and termination lemmas over any finite coefficient
field. Inspection of `localUpperRamificationGroup` in check
`026ed14f-8f9e-4f56-b713-7db5efc8468d` reported only `propext`,
`Classical.choice` and `Quot.sound`. Independent review, whole-Library machine
validation and publication remain separate requirements.
