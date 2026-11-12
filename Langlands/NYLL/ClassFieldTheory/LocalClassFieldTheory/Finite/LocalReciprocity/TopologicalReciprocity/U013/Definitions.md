# Continuous norm-class projection (M257.013)

`Langlands.NYLL.LocalClassFieldTheory.normClassContinuous` bundles the
published canonical projection `Langlands.NYLL.LocalFieldTheory.normClass`
as a continuous multiplicative homomorphism for the native quotient topology.
Its complete elaborated telescope is

```lean
(K L : Type) [Field K] [Field L] [Algebra K L] [TopologicalSpace K] :
  Kˣ →ₜ* Langlands.NYLL.LocalFieldTheory.NormQuotient K L
```

Both fields are in `Type 0`, and there are no universe parameters. The
source's enclosing section also declares `ValuativeRel K`,
`IsNonarchimedeanLocalField K`, `FiniteDimensional K L` and `IsGalois K L`.
None occurs in the definition's type or body, so Lean omits all four from
the elaborated declaration. A private check reconstructs the entire source
section, including these hypotheses, and compares its definition with this
whole unapplied constant by reflexivity. A second full-constant comparison
uses the concrete Mathlib quotient projection and explicitly specifies
`QuotientGroup.instTopologicalSpace`. Thus the extraction retains the complete
source telescope, rather than generalizing a theorem with extra assumptions.
No topology on `L`, compatibility premise or local-field hypothesis is added.

## Construction and dependencies

The source definition body is retained:

```lean
  { normClass K L with
    continuous_toFun := QuotientGroup.continuous_mk }
```

The underlying homomorphism is the published `normClass K L` from
`NormQuotient.U005.Definitions`. This is Mathlib's canonical quotient
homomorphism from `Kˣ` to `Kˣ` modulo the published actual norm image
`localNormSubgroup K L`. Its pointwise value is the coset
`QuotientGroup.mk x`; no new quotient, norm convention or projection is
introduced. The field norm used by the existing subgroup is Mathlib's
general `Algebra.norm K`, whose definition requires no finite-dimensionality
premise. The present construction works for that same general subgroup.

The other direct import is the published
`TopologicalReciprocity.U001.Definitions`, whose source-local
`Langlands.NYLL.PortInternal.M257.d001` supplies the native quotient topology.
The local instance attribute is restored only inside this module. Its body
is definitionally Mathlib's `QuotientGroup.instTopologicalSpace` on the actual
quotient of the native units topology. The units topology is induced from
the given topology on `K`. Consumers can restore `d001` locally as needed;
this module exports no global topology or discreteness instance.

Mathlib's `QuotientGroup.continuous_mk` proves continuity of the actual
quotient projection for any topology on the underlying group. No
`IsTopologicalGroup Kˣ` premise is needed for this projection. The structure
update retains the published homomorphism and uses this proof for its
`continuous_toFun` field. Private checks verify the complete source-shaped
constant, its concrete topology, the underlying homomorphism, evaluation on
a representative, continuity, and the absence of a newly exported topology
instance. They compile without errors or warnings in the approved environment.

This focused check establishes a smaller dependency set than the conservative
partition predecessor M257.012.END: M257.013 needs only the already published
norm-class projection, source-local quotient topology and their Mathlib
imports. It does not depend on the local reciprocity equivalence or its
underlying-equivalence theorem, norm-subgroup openness, quotient discreteness,
or an Artin map. This definition supplies the continuous projection data;
it does not construct reciprocity or the continuous local Artin map.

## Source correspondence and modifications

| Source unit | Original declaration | Adapted declaration | Lines |
| --- | --- | --- | --- |
| M257.013 | `LocalClassFieldTheory.normClassContinuous` | `Langlands.NYLL.LocalClassFieldTheory.normClassContinuous` | 395–398; docstring 393–394 |

The pinned source is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean`.
Its SHA-256 is
`28cfb0b56b885089511a7372bfe3bf5e80d444fb91d1e982ba0b5647d26d0108`.
The complete original module was read, including the source-local instance
at lines 36–41 and the enclosing section at lines 347–351. Registered source:
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The related supplement registration is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum for either registration was found in the current
Library errata directory.

Worker 120 extracted this one definition, prefixed the namespace with
`Langlands.NYLL`, used the two focused published imports, restored the local
topology attribute, and omitted section variables that Lean does not retain.
The Type-zero boundary, effective parameter order, docstring, noncomputable
status and construction body are preserved. No external project import,
patch10 code or other worker's draft is reused. Library and task searches
found no existing declaration or task for this unit.

The original 2026 Naganori Yamaguchi copyright and authorship header is
retained verbatim, including the assistance credit to OpenAI Codex. The
unchanged Apache-2.0 `LICENSE` and `NOTICE` are already published at
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Their respective SHA-256
values are `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
verified against the retained originals. The source NOTICE has no entry
specific to TopologicalReciprocity. The extraction and modifications are
also recorded in the Lean header.
