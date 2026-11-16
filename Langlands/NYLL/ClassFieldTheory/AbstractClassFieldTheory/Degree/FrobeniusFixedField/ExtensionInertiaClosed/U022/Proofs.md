# The relative inertia subgroup is closed

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.extensionInertiaWithin_isClosed`, the proof phase of
M014.022 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m014).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.extensionInertiaWithin_isClosedStatement` applied to the
theorem's parameters:

```lean
theorem extensionInertiaWithin_isClosed (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) :
    extensionInertiaWithin_isClosedStatement D K L hLK
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : Type u} [Group G] [TopologicalSpace G]`. The theorem takes `D`, the instance `[IsTopologicalGroup G]`, `K`, `L` and `hLK`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.ExtensionInertiaClosed.Statements`, the target is the proposition

```lean
IsClosed (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup)
```

Here `D : DegreeData G` (M010.002) is a degree datum, a continuous homomorphism `D.degree : G →ₜ* ZHatMul` onto `ZHatMul = Multiplicative ZHat` (M010.001, M008.008), `K : FiniteResidueAbstractField D` (M010.021) is an abstract field with closed subgroup `K.field = G_K` and finite residue quotient, `L : ClosedSubgroup G` is a closed subgroup with `hLK : L.toSubgroup ≤ K.field.toSubgroup`, and `D.extensionInertiaWithin K.field L hLK` (M012.002) is the subgroup `L.toSubgroup.subgroupOf K.field.toSubgroup ⊓ D.fieldInertiaWithin K.field` of `G_K`, where `D.fieldInertiaWithin K.field` (M010.014) is the kernel of the restricted degree `D.restrictedDegree K.field : G_K →ₜ* ZHatMul` (M010.008); that is the inertia subgroup `I_L` of `L` viewed inside `G_K`. The target says that this subgroup is closed in `G_K` with the subspace topology. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.ExtensionInertiaClosed.Statements`, which defines the target and imports `extensionInertiaWithin` (M012.002), `fieldInertiaWithin` (M010.014), `restrictedDegree` (M010.008), `FiniteResidueAbstractField` (M010.021) and, through the degree data module, `ZHat` with its published `T2Space ZHat` instance (M008.012).

The module opens no namespace. The source's `open CyclicCohomology` is not needed, because the published `extensionInertiaWithin` is stated with the Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup` of the source's `extensionSubgroup K L hLK`.

## Implemented proof

After `show` states the published proposition unfolded, the proof is the source proof. `hE` shows that `L.toSubgroup.subgroupOf K.field.toSubgroup` is closed: its carrier is, by `change`, the preimage of the closed set `L` under the continuous inclusion `G_K → G` (`L.isClosed'.preimage continuous_subtype_val`). `hI` shows that `D.fieldInertiaWithin K.field` is closed: after installing `T2Space ZHatMul` from the published `T2Space ZHat` (by `change`), its carrier is, by `change`, the set `{x | D.degree x.1 = 1}`, closed by `isClosed_eq` applied to the continuous map `(D.restrictedDegree K.field).continuous_toFun` and a constant. Finally `change` writes the target's carrier as that of the infimum `L.toSubgroup.subgroupOf K.field.toSubgroup ⊓ D.fieldInertiaWithin K.field`, and `hE.inter hI` closes it. The source writes `extensionSubgroup K.field L hLK` in `hE` and in the final `change`; the port writes its Mathlib body `L.toSubgroup.subgroupOf K.field.toSubgroup`, which is how the published `extensionInertiaWithin` (M012.002) is stated.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`, lines 446–464](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean#L446-L464):
the docstring at line 446 and the theorem at lines 447–464. It lies in `namespace ClassFormation` (line 19), with `open CyclicCohomology` (line 21), its `noncomputable section` (line 25), `universe u` (line 27), the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 29) and `namespace DegreeData` (line 300). The source is:

```lean
/-- The extension's inertia subgroup is closed inside its base subgroup. -/
theorem extensionInertiaWithin_isClosed (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) :
    IsClosed (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup) := by
  have hE : IsClosed (extensionSubgroup K.field L hLK : Set K.field.toSubgroup) := by
    change IsClosed ((fun x : K.field.toSubgroup => (x : G)) ⁻¹' (L : Set G))
    exact L.isClosed'.preimage continuous_subtype_val
  have hI : IsClosed (D.fieldInertiaWithin K.field : Set K.field.toSubgroup) := by
    let : T2Space ZHatMul := by
      change T2Space ZHat
      infer_instance
    change IsClosed {x : K.field.toSubgroup | D.degree x.1 = 1}
    exact isClosed_eq
      (D.restrictedDegree K.field).continuous_toFun continuous_const
  change IsClosed
    ((extensionSubgroup K.field L hLK ⊓ D.fieldInertiaWithin K.field) : Set K.field.toSubgroup)
  exact hE.inter hI
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`;
its SHA-256 is `cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `extensionInertiaWithin_isClosedStatement D K L hLK` as its type, and begin the proof with `show` stating it unfolded;
- write the source's `extensionSubgroup K.field L hLK` (twice) as its Mathlib body `L.toSubgroup.subgroupOf K.field.toSubgroup`, the form of the published `extensionInertiaWithin`, and wrap the lines that this lengthens;
- omit `open CyclicCohomology` and all other source declarations.

The theorem's name, docstring, binders and the remaining proof steps are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M014.022. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
