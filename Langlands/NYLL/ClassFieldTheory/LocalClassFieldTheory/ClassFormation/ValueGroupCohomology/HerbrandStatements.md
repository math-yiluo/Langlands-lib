# NYLL M141.004, .006, .009 and .010: value-group Herbrand statements

The paired Lean file supplies four proposition targets concerning the actual
norm subgroups and low-degree Herbrand groups of the trivially acted-on integer
value group. It preserves the source propositions and their local action
bindings. It supplies no proofs of these targets.

## Pinned source and correspondence

The source is Naganori Yamaguchi's ClassFieldTheory (NYLL), commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/ValueGroupCohomology.lean`,
retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its SHA-256 is
`6ee54afe1a8a664d94bff689a3725f8fa4a92aa4054f0f371c7d199074ec59e9`.
The complete source file was read, including the section context and the local
instances of the later cardinality statements.

The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
folder `n-yamaguchi-0729--ClassFieldTheory/source`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The inventory is `notes/reuse/nyll-public-port/m121-m144.md`, section M141.
No applicable source erratum is recorded in the Library's `notes/errata/`.

The original declarations are in `LocalClassFieldTheory`. The adapted
declarations below are in `Langlands.NYLL.LocalClassFieldTheory`.

| Unit | Original declaration | Source statement lines | Adapted declaration |
| --- | --- | --- | --- |
| M141.004 | `galoisGroupValueGroupFixedToZModHom_ker` | 76–80 | `galoisGroupValueGroupFixedToZModHom_kerStatement` |
| M141.006 | `galoisGroupValueGroupHerbrandH0Finite` | 132–134 | `galoisGroupValueGroupHerbrandH0FiniteStatement` |
| M141.009 | `galoisGroupValueGroup_normKernelSubgroup_eq_bot` | 166–168 | `galoisGroupValueGroup_normKernelSubgroup_eq_botStatement` |
| M141.010 | `galoisGroupValueGroupHerbrandHMinusOneFinite` | 186–190 | `galoisGroupValueGroupHerbrandHMinusOneFiniteStatement` |

## Common telescope and actual objects

Source lines 16–31 introduce the namespaces, `noncomputable section`,
`open scoped BigOperators`, one arbitrary universe `u`, and the complete
variable telescope:

```lean
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]
```

Every target keeps these two explicit type binders and the four instance
binders, in that order. M141.010 then takes the explicit binder
`(σ : Gal(L/K))`, also in the source order. Here `Gal(L / K)` is the actual
group of `K`-algebra automorphisms of `L`; its canonical finite type is supplied
by the finite-dimensional field extension. There is no separately supplied
group or finite-type parameter.

Each proposition begins with the source's local instance:

```lean
letI := galoisGroupValueGroupMulDistribMulAction K L
```

The imported M140.005 definition makes `Gal(L / K)` act trivially on
`Multiplicative Int`. It is selected locally, with the same scope as in the
source. This file registers no global instance.

The imported M141.002 definition
`galoisGroupValueGroupFixedToZModHom K L` is the actual homomorphism from the
fixed subgroup to `Multiplicative (ZMod (Fintype.card (Gal(L / K))))`.
It composes the fixed-subgroup inclusion with the multiplicative form of
`Int.castAddHom`.

The imported M113 definitions in
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` are:

- `fixedSubgroup G A`, the elements fixed by every element of `G`;
- `tateNormHom`, the homomorphism with value `tateNorm G A a = ∏ g : G, g • a`;
- `tateNormSubgroup G A`, its image, and `normKernelSubgroup G A`, its kernel;
- `augmentationSubgroup G A σ`, the image of `a ↦ σ • a * a⁻¹`;
- `HerbrandH0 G A`, the quotient of `fixedSubgroup G A` by
  `(tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)`;
- `HerbrandHMinusOne G A σ`, the quotient of `normKernelSubgroup G A` by
  `(augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)`.

These are published constructions, imported by Lean name. No subgroup,
quotient, action or proof field is replaced by an assumed object.

## The four proposition bodies

M141.004 asserts equality of two actual subgroups of the fixed subgroup:

```lean
letI := galoisGroupValueGroupMulDistribMulAction K L
MonoidHom.ker (galoisGroupValueGroupFixedToZModHom K L) =
  (tateNormSubgroup (Gal(L / K)) (Multiplicative Int)).subgroupOf
    (fixedSubgroup (Gal(L / K)) (Multiplicative Int))
```

Thus the kernel of reduction modulo the automorphism-group order is exactly
the norm image restricted to the fixed subgroup. The use of `subgroupOf`
matches the source; the statement does not identify subgroups of different
ambient groups.

M141.006 asserts:

```lean
letI := galoisGroupValueGroupMulDistribMulAction K L
Finite (HerbrandH0 (Gal(L / K)) (Multiplicative Int))
```

This is a finiteness proposition about the actual degree-zero quotient. It
does not assume finiteness of that quotient or of the coefficient group.

M141.009 asserts:

```lean
letI := galoisGroupValueGroupMulDistribMulAction K L
normKernelSubgroup (Gal(L / K)) (Multiplicative Int) = ⊥
```

The right side is the trivial subgroup of the multiplicative integer value
group. This target states the vanishing of the norm kernel.

M141.010, for each supplied automorphism `σ`, asserts:

```lean
letI := galoisGroupValueGroupMulDistribMulAction K L
Finite
  (HerbrandHMinusOne (Gal(L / K)) (Multiplicative Int) σ)
```

It uses the source's chosen-sigma quotient. The source requires no cyclicity
or generator hypothesis for this target. None of the four targets requires
`IsGalois K L`, a valuation, topology, local-field structure or integral closure.

## Modifications and reuse

Worker 230 made the following changes:

- Extract only the four source statement types listed above. Replace each
  `theorem` with `def ...Statement : Prop :=` and use its original proposition
  as the body. Omit the original proof and declaration docstring.
- Prefix the enclosing namespace and the opened NYLL namespaces with
  `Langlands.NYLL`. Retain the universe, common `variable` command,
  noncomputable section and scoped notation.
- Replace the original four imports with the published
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology.Definitions`
  and
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions`.
  The former supplies the original Mathlib imports and the action and
  reduction-homomorphism definitions. The latter supplies the actual M113
  data, whose norm and sigma-minus-one homomorphism fields use the separately
  published source proofs.
- Replace the module description with an explicit modification notice, retaining
  the original copyright, Apache-2.0 release and author header.

The current Library was checked by these exact declaration names before
authoring; none of the four targets was already present. The previously
published M141.001–.003 pair is reused without edits.

## Scope and attribution

These four definitions are proposition targets for separate proof tasks.
They do not establish the corresponding finiteness or subgroup equalities.
The later M141 cardinality targets are separate obligations: their source
statements locally bind the actual M141.006 or M141.010 proof, which this
file does not supply. The M141.005 equivalence data likewise has its own
source proof prerequisites. No class-formation, Herbrand-quotient
multiplicativity, Tate, transfer, cup-product or reciprocity theorem is claimed.

The original author is Naganori Yamaguchi, assisted by OpenAI Codex. The retained
license and notice are `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
No unpublished draft or additional source was reused.
