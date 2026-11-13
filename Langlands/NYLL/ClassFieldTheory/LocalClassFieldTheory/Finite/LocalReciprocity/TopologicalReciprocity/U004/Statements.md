# Compactness and intersection targets for integer-unit norms (M257.004–005)

This pair defines two unproved proposition targets from the pinned NYLL
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean`.
Both concern the published subgroup `Langlands.NYLL.PortInternal.M257.d003 K L`
of `Kˣ`. It is the image of the units of the valuation-integer subring `𝒪[L]`
under the field norm, that is, the range of the composite of
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits L`
with `Langlands.NYLL.LocalFieldTheory.normUnits K L`.

| Source unit and original name | Adapted target | Original lines |
| --- | --- | --- |
| M257.004, private `LocalClassFieldTheory.integerUnitNormSubgroup_isCompact` | `Langlands.NYLL.PortInternal.M257.d004Statement` | 59–70 (signature 59–63) |
| M257.005, private `LocalClassFieldTheory.integerUnitNormSubgroup_eq_localNormSubgroup_inf_baseUnits` | `Langlands.NYLL.PortInternal.M257.d005Statement` | 72–123 (signature 72–83) |

Both source theorems are in the section `NormSubgroupTopology`. They share its
declared universe `u` (source line 45). The two fields of each target are in
that same arbitrary universe `u`.

## Exact scope

`d004Statement` has the source telescope

```lean
(K L : Type u) [NontriviallyNormedField K] [NormedField L]
[NormedAlgebra K L] [FiniteDimensional K L] [CompleteSpace K]
[ValuativeRel L] [CompactSpace 𝒪[L]]
```

It asserts `IsCompact (d003 K L : Set Kˣ)`. The topology on `Kˣ` is Mathlib's
standard units topology `Units.instTopologicalSpaceUnits`. It is induced by the
embedding `u ↦ (u, u⁻¹)` into `K × Kᵐᵒᵖ`, with the topology of the given norm
on `K`. The compactness hypothesis is for the subspace topology of `𝒪[L]` in
the normed topology of `L`. The valuation `ValuativeRel L` is an independent
hypothesis. Nothing in the target relates it to the norm of `L`, exactly as in
the source. There is no valuation on `K`, local-field, Galois or separability
premise. Thus d004 asserts that the norm of a finite-dimensional normed
extension maps the units of a compact valuation-integer subring of `L` to a
compact subset of `Kˣ`.

`d005Statement` has the source telescope

```lean
(K L : Type u)
[Field K] [ValuativeRel K] [TopologicalSpace K]
[_root_.IsNonarchimedeanLocalField K]
[Field L] [ValuativeRel L] [TopologicalSpace L]
[_root_.IsNonarchimedeanLocalField L]
[Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
[Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]
[IsIntegralClosure 𝒪[L] 𝒪[K] L]
```

It asserts the equality of subgroups of `Kˣ`

```lean
d003 K L =
  Langlands.NYLL.LocalFieldTheory.localNormSubgroup K L ⊓
    Langlands.NYLL.LocalFieldTheory.localBaseUnitSubgroup K
```

`localNormSubgroup K L` is the range of the field norm `normUnits K L` on `Lˣ`.
`localBaseUnitSubgroup K` is the image of `𝒪[K]ˣ` in `Kˣ`. So d005 says that
the norms of integer units of `L` are exactly the norms that are integer units
of `K`. `IsNonarchimedeanLocalField` is Mathlib's root class (no NYLL class of
that name exists); `_root_` only makes this explicit. The algebra
`𝒪[K] → 𝒪[L]` used by the integral-closure hypothesis is Mathlib's
`Valuation.HasExtension.instAlgebraInteger`, derived from the
valuation-extension hypothesis. The algebra `𝒪[K] → L` is
`Algebra.ofSubsemiring`, through `K`. Both elaborate as in the source. The
separability, valuation-extension and integral-closure hypotheses are all
retained. The topological spaces of `K` and `L` are retained as independent
structure parameters, constrained only by the local-field classes. The
assertion itself uses no topology.

Here `𝒪[R]` is Mathlib's scoped `ValuativeRel` notation
`Valuation.integer (ValuativeRel.valuation R)`, the notation the source opens.

These definitions prove neither assertion. They add no hypothesis or
conclusion, and introduce no instance.

## Published dependencies and modifications

The file imports, by Lean name:

- `Langlands.NYLL.PortInternal.M257.d003` from
  `TopologicalReciprocity.U002.Definitions` (source M257.003, the private
  `integerUnitNormSubgroup`).
- `Langlands.NYLL.LocalFieldTheory.localNormSubgroup` from
  `NonarchimedeanLocalField.NormQuotient.U001.Definitions` (source
  `LocalFieldTheory.localNormSubgroup`).
- `Langlands.NYLL.LocalFieldTheory.localBaseUnitSubgroup` from
  `NonarchimedeanLocalField.UnitTopology.U001.Definitions` (source M256.001,
  `LocalFieldTheory.localBaseUnitSubgroup`).

These are the only definitions with these names in the pinned source.

Worker 25 made the following changes. The source-private theorems receive the
inventory's stable names `d004` and `d005`, with `Statement` appended. Each
theorem becomes a `def` returning `Prop` with the source conclusion as its body,
and its proof is removed. References use the published names. The source
namespace `LocalClassFieldTheory` and its section are replaced by
`Langlands.NYLL.PortInternal.M257`, and the common `universe u` is declared at
file level. The source's `ValuativeRel` scope is retained. The unused `NNReal`
scope and the `open` lines for `LocalFieldTheory` and
`LocalFieldTheory.IsNonarchimedeanLocalField` are replaced by qualified names.
All binders, their order and their hypotheses are as in the source.

The full source imports are replaced by the published definitions above and the
Mathlib modules for normed modules in finite dimension, the local-field class,
separability, valuation extensions and integral closures. The source-local
quotient topology M257.001 does not occur in either assertion and is not
imported. No Artin map, class-formation input or norm-index theorem is needed
to state these targets. They remain proof obligations: the source proves d004
from continuity of the norm and of the integer-unit inclusion, and d005 from
the valuation formula for separable norms. A Library search found no published
equivalent of either assertion.

## Checks

Compilation in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` succeeded
with no errors or warnings. The diagnostics are
`0ceae9de-cc35-4bd4-a55c-62af7b88d57c` for `d004Statement` and
`b27630f5-9bfb-4133-a8ad-159fdc60595f` for `d005Statement`. For each
declaration, inspection reports `statement_returns_prop: true` and the single
universe parameter `u`. A private probe (diagnostic
`a2f534df-1ea2-46bd-9f45-e66e4edc4123`) checked the following:

- Both full dependent types are equal by `rfl` to the source telescopes ending
  in `Prop`.
- `d004Statement` unfolds by `Iff.rfl` to compactness, in
  `Units.instTopologicalSpaceUnits`, of the range of the original composite
  norm map. Its compactness hypothesis may be given for the subtype topology of
  `𝒪[L]` in `L`.
- `d005Statement` unfolds by `Iff.rfl` to the equality of that range with
  `(normUnits K L).range ⊓ MonoidHom.range (integerUnitsToFieldUnits K)`.
- In the d005 telescope, instance synthesis gives the algebra structures named
  above.

Both declarations depend only on `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance and attribution

The source is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The original module SHA-256 is
`28cfb0b56b885089511a7372bfe3bf5e80d444fb91d1e982ba0b5647d26d0108`.
Source registration: `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`.
The original copyright and author header, including assistance credit to
OpenAI Codex, is retained verbatim. The source is Apache-2.0. Its license and
notice are unchanged at `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The source NOTICE has no entry specific to this module. The extraction, naming,
proof removal and import changes are recorded above and in the Lean header.
No patch or other worker's draft is reused.
