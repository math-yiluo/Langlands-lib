# The spectral valuation on a finite extension extends the base valuation: statement

This module defines the closed proposition
`Langlands.NYLL.LocalFieldTheory.finiteExtensionSpectralValuation_hasExtensionStatement`,
the statement phase of source row M270.009. It packages the complete source
theorem signature as a `def` returning `Prop` and supplies no proof. A later
proof child will prove it under the name
`Langlands.NYLL.LocalFieldTheory.finiteExtensionSpectralValuation_hasExtension`.

## Parameters and local instances

The proposition universally quantifies, in order,

```lean
(K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]
  [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

exactly as the source theorem does, with both fields in `Type` (universe
zero), as in the source. The field `L` carries no valuative relation or
topology of its own among the parameters. The proposition then installs
two local instances on `L`:

```lean
letI : NontriviallyNormedField L :=
  Langlands.LocalField.FiniteExtension.normedField K L
letI : ValuativeRel L := Langlands.LocalField.FiniteExtension.valuativeRel K L
```

Both are published Library declarations in
`Langlands/LocalField/FiniteExtension.lean`, reused by name:

- `Langlands.LocalField.FiniteExtension.normedField K L` is Mathlib's
  `spectralNorm.nontriviallyNormedField K L`, the spectral norm on `L`
  over the canonical norm `Langlands.LocalGalois.localNormedField K` of the
  local field `K`.
- `Langlands.LocalField.FiniteExtension.valuativeRel K L` is
  `ValuativeRel.ofValuation (Langlands.LocalGalois.spectralValuation K L)`,
  the valuative relation of the spectral valuation.

The normed-field instance does not occur in the conclusion. It is kept so
that the proposition has the same local-instance context as the source
theorem. No global instance is introduced.

## Conclusion

After the local instances, the proposition is

```lean
Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)
```

Here `ValuativeRel.valuation K` is Mathlib's canonical valuation for the
supplied relation on `K`, and `ValuativeRel.valuation L` is the canonical
valuation for the spectral relation installed above. Mathlib's class
`Valuation.HasExtension vR vA` has the single field
`val_isEquiv_comap : vR.IsEquiv (vA.comap (algebraMap R A))`. So the
statement says: for all `x y : K`, `valuation K x ≤ valuation K y` holds
exactly when `valuation L (algebraMap K L x) ≤ valuation L (algebraMap K L y)`.
The algebra map is the supplied `Algebra K L`.

## Relation to existing Library declarations

The source unit M270.009 refers to three source definitions and one source
theorem. All of them are already covered by published Library declarations,
and this module uses those Library declarations instead of porting them:

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M270.001, `LocalFieldTheory.localFieldNontriviallyNormedField` | `Langlands.LocalGalois.localNormedField` (the base norm inside `normedField`) |
| M270.003, `LocalFieldTheory.finiteExtensionSpectralNormedField` | `Langlands.LocalField.FiniteExtension.normedField` |
| M270.007, `LocalFieldTheory.finiteExtensionSpectralValuativeRel` | `Langlands.LocalField.FiniteExtension.valuativeRel` |
| M270.008, `LocalFieldTheory.finiteExtensionSpectralIsNonarchimedeanLocalField` | `Langlands.LocalField.FiniteExtension.isLocalField` |

A review of an earlier candidate found the Library definitions
definitionally equal to the source definitions M270.001, M270.003 and
M270.007. The source M270.007 builds the relation from the valuation
`x ↦ ‖x‖₊` of the spectral norm, and the Library relation builds it from
`LocalGalois.spectralValuation K L`, the same spectral norm viewed as a
valuation. M270.008 is not needed by this statement.

The mathematical content of M270.009 is close to the published Library
theorem `Langlands.LocalField.FiniteExtension.algebraMap_vle_iff`, which says
that `algebraMap K L x ≤ᵥ algebraMap K L y ↔ x ≤ᵥ y` for the Library relation
`valuativeRel K L`. That theorem is phrased with the relations `≤ᵥ`, not as an
instance of Mathlib's class `Valuation.HasExtension` between the canonical
valuations. The two forms are related through Mathlib's
`Valuation.Compatible.vle_iff_le`. The Library has no public declaration
with this `Valuation.HasExtension` conclusion between the two canonical
valuations. The closest public one is the instance
`Langlands.LocalGalois.spectralValuation_extends` in
`Langlands/Galois/Local/SpectralDefinitions.lean`. It states
`(NormedField.valuation (K := K)).HasExtension (spectralValuation K L)` for
a complete ultrametric normed base field. Both of its valuations take
values in `ℝ≥0`. Its base valuation is the norm valuation, not
`ValuativeRel.valuation K`, and its extension valuation is the spectral
valuation itself, not the canonical valuation of `valuativeRel K L` with
values in `ValuativeRel.ValueGroupWithZero L`. So it is a different
proposition. Two Library modules prove a similar instance privately:
`canonicalValuationHasExtension` in
`Langlands/GroupScheme/IntegralModel/ValuedIntegralPointDescent.lean`
(for any `ValuativeExtension F L`, and `private`) and
`spectralExtendsCanonical` in
`Langlands/GroupScheme/IntegralModel/SpectralIntegralPointAction.lean`
(to `spectralValuation F L` itself rather than to the canonical valuation of
`valuativeRel`, and `private`). Neither can be reused by name. The
`Valuation.HasExtension` form is the one the source later installs as an
instance argument, for example in the definition M284.002
(`ambientEmbeddedPrimeWitness`). That is why this statement is published
separately. The proof child is expected to derive it from
`algebraMap_vle_iff`.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionTopology.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionTopology.lean>).
The complete file was read and its SHA-256 verified as
`62f5ffd2e815d3b14c80abb812cfc839d329043a43e8da5c9f29cd655d222b8f`.
The selected docstring, signature and proof occupy lines 178–218; the
theorem begins at line 180. The header occupies lines 1–5, the module
docstring lines 12–19, the `noncomputable section` line 23, the namespace
line 25 and the `open scoped NNReal ValuativeRel` line 27. The replaced
source definitions occupy lines 29–44 (M270.001), 66–77 (M270.003) and
132–145 (M270.007).

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M270.009, `LocalFieldTheory.finiteExtensionSpectralValuation_hasExtension` | `Langlands.NYLL.LocalFieldTheory.finiteExtensionSpectralValuation_hasExtensionStatement`, closed Prop target |
| Same source theorem, later proof phase | `Langlands.NYLL.LocalFieldTheory.finiteExtensionSpectralValuation_hasExtension`, reserved for the proof child |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the source theorem:

- The theorem becomes a Prop-valued definition with the `Statement`
  suffix. Its explicit parameters become universal binders in the same
  order, and the proof (source lines 190–218) is omitted for the separate
  proof phase.
- The namespace `LocalFieldTheory` is prefixed with `Langlands.NYLL`.
- The two local instances use the Library's
  `Langlands.LocalField.FiniteExtension.normedField` and
  `Langlands.LocalField.FiniteExtension.valuativeRel` in place of the
  source's M270.003 and M270.007, as described above.
- The source imports (`Nyll...NonarchimedeanLocalField.Basic`,
  `Nyll...NonarchimedeanLocalField.ValuedTopology`,
  `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` and
  `Mathlib.RingTheory.Valuation.Extension`) are replaced by the single
  import `Langlands.LocalField.FiniteExtension`. It provides the Library
  structures and, through its dependencies, Mathlib's spectral norm and
  `Valuation.HasExtension`.
- The `noncomputable section` and the unused `open scoped NNReal
  ValuativeRel` are omitted. All other declarations of the source file are
  omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M270.009 statement target. Its proof and the
source rows M270.010 (`finiteExtensionSpectralNormedAlgebra`) and M270.011
(`finiteExtensionSpectralValuation_hasExtension_of_tower`) are not part
of this unit.
