# Relative abstract fixed fields: Galois, finiteness and degree targets

Adapted by Worker 4913 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`
(SHA-256 `d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`).
The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, and the
supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M099.012 | theorem `abstractRelativeFixedField_isGalois` (docstring 182–183, signature 184–189, proof 190–192) | `abstractRelativeFixedField_isGaloisStatement` |
| M099.019 | theorem `abstractRelativeFixedField_finiteDimensional` (docstring 337–338, signature 339–347, proof 348–363) | `abstractRelativeFixedField_finiteDimensionalStatement` |
| M099.020 | theorem `finiteAbstractExtension_degree_eq_finrank` (docstring 365–366, signature 367–377, proof 378–404) | `finiteAbstractExtension_degree_eq_finrankStatement` |

Every unqualified original name is in the source namespace
`LocalClassFieldTheory`; every adapted name is in
`Langlands.NYLL.LocalClassFieldTheory`. Each adapted declaration is a `def`
returning `Prop` whose body is the source theorem statement. None has a proof
here; the proofs are separate tasks, which may use the source theorem names
in the same namespace.

## Parameters

The source theorems take the section variables of line 31,

```lean
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
```

followed by their own binders. A source theorem keeps an instance-implicit
section variable whose variables it mentions, so all three source theorems
have `[IsGalois k Ω]` in their telescope, even though their statements do not
need it. A definition keeps only the section variables its type or body uses,
which would drop `[IsGalois k Ω]` here. Each adapted definition therefore
writes the five section variables as its own leading binders, in the source
order and with the source binder kinds. The full telescopes are:

```lean
abstractRelativeFixedField_isGaloisStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) : Prop

abstractRelativeFixedField_finiteDimensionalStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) : Prop

finiteAbstractExtension_degree_eq_finrankStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) : Prop
```

`#check` confirms these telescopes, with `[IsGalois k Ω]` present in all
three. Both fields are in `Type` (universe zero), as in the source. The
hypotheses `hnormal` (M099.012, M099.020) and `hKfinite` (M099.019, M099.020),
and `hLKfinite` in M099.019, do not occur in the propositions. They are kept
because they are source hypotheses. Where Lean's unused-variables linter is
reported, it flags these five binders as not explicitly referenced; the
warnings do not affect the statements. In M099.020, `hLKfinite` is a local instance, as in
the source, and supplies the finiteness instance argument of `ofInclusion`.

## The three propositions

Let `L ≤ K` be closed subgroups of `Gal(Ω/k)`, with inclusion proof `hLK`.
`abstractFixedField k Ω K` is the fixed field of `K`, an intermediate field of
`Ω / k`. `abstractRelativeFixedField k Ω hLK` is the fixed field of `L`
regarded, by `IntermediateField.extendScalars`, as an intermediate field of
`Ω` over `abstractFixedField k Ω K`. `extensionSubgroup K L hLK` is `L`
viewed as a subgroup of the group `K`.

- `abstractRelativeFixedField_isGaloisStatement` concludes
  `IsGalois (abstractFixedField k Ω K) (abstractRelativeFixedField k Ω hLK)`:
  if `L` is normal in `K`, the fixed field of `L` is Galois over the fixed
  field of `K`.
- `abstractRelativeFixedField_finiteDimensionalStatement` concludes
  `FiniteDimensional (abstractFixedField k Ω K) (abstractRelativeFixedField k Ω hLK)`:
  if `K` has finite index in the whole Galois group (written as the
  distinguished base field `baseField (Gal(Ω/k))`, whose subgroup is `⊤`) and
  `L` has finite index in `K`, the fixed field of `L` is finite-dimensional
  over the fixed field of `K`.
- `finiteAbstractExtension_degree_eq_finrankStatement` concludes
  `((DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ) = Module.finrank (abstractFixedField k Ω K) (abstractRelativeFixedField k Ω hLK)`:
  under all three hypotheses, the degree of the finite abstract extension
  `L | K` (a positive natural number, the cardinality `Nat.card` of the coset
  space of `L` in `K`) equals the field degree of the fixed field of `L` over
  the fixed field of `K`.

## Library declarations used

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`) |
| M010.003, `ClassFormation.baseField` | `Langlands.NYLL.ClassFormation.baseField` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`) |
| M010.005, `ClassFormation.le_baseField` | `Langlands.NYLL.ClassFormation.le_baseField` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`) |
| M010.068, `ClassFormation.DegreeData.FiniteAbstractExtension.ofInclusion` | `Langlands.NYLL.ClassFormation.DegreeData.FiniteAbstractExtension.ofInclusion` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions`) |
| M099.001, `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions`) |
| M099.009, `LocalClassFieldTheory.abstractRelativeFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Definitions`) |

All are used under their published names; none is replaced by its body. The
published `le_baseField K` has the type `le_baseFieldStatement K`, which
unfolds to the source inclusion `K.toSubgroup ≤ (baseField G).toSubgroup`. It
occurs only as the proof argument of `extensionSubgroup`, which ignores it.
The published `ofInclusion` states its instance argument as
`Finite (base.toSubgroup ⧸ field.toSubgroup.subgroupOf base.toSubgroup)`,
which is `extensionSubgroup` unfolded; instance search finds `hLKfinite` for
it through the reducible abbreviation.

## Modifications and attribution

Worker 4913 made these changes to the three source theorems:

- Each theorem becomes a Prop-valued `def` with the `Statement` suffix,
  keeping the theorem binders in source order and the statement text. The
  proofs are omitted.
- The section variables of line 31 are written as explicit leading binders of
  each definition, as explained above, instead of a `variable` command.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
  Of the source `open RamificationTheory KummerTheory CyclicCohomology` (line
  23) and `open ClassFormation` (line 25), `CyclicCohomology` and
  `ClassFormation` are kept and the unused `RamificationTheory` and
  `KummerTheory` are omitted. The `noncomputable section` of line 29 is kept.
- The M099.019 docstring "The same relative finiteness statement in the
  scalar-extended ..." becomes "The relative finiteness statement in the
  scalar-extended ...", since the source theorem it refers to (M099.018) is
  not in this file. The other two docstrings are unchanged.
- The source imports (lines 7–10) are replaced by the published modules
  listed above. All other declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0 notice,
and its module docstring records these modifications. The Library's
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) retain the
original license and notices.

This unit contains only the M099.012, M099.019 and M099.020 statement
targets. It makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
