# NYLL M015.001, M015.002 and M015.004: the Frobenius semigroup

This file adapts three declarations of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`d11fc29514c9a12171d2a10287d09d10aa13b765641c57893c102aa7a6a70a06`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, with the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Unit | Kind | Source lines (docstring, declaration) | Original name after `ClassFormation.DegreeData.` | Adapted name |
| --- | --- | --- | --- | --- |
| M015.001 | def | 28, 29–42 | `frobeniusMul` | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusMul` |
| M015.002 | instance | 44–47, 48–54 | `frobeniusElementsMul` | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusElementsMul` |
| M015.004 | instance | 67, 68–77 | `frobeniusElementsSemigroup` | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusElementsSemigroup` |

The body of M015.001 uses the proofs of the source theorems M014.013
`frobeniusExponent_pos` and M014.014
`extensionNormalizedDegree_frobenius_eq_pow` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`
(SHA-256 `cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`;
statements lines 310–315 and 319–326, proofs lines 316 and 327), as
described below.

## The objects

Every object used is a source definition published in the Library or a
Mathlib definition. No replacement degree datum, field, inertia group,
normalized degree or Frobenius element is introduced.

- `D : DegreeData G` (M010.002) is the source degree datum, and
  `K : FiniteResidueAbstractField D` (M010.021) bundles a closed subgroup
  `K.field` of `G` with finiteness of its residue quotient.
- `L : ClosedSubgroup G` with `hLK : L.toSubgroup ≤ K.field.toSubgroup` is
  the extension. `L.toSubgroup.subgroupOf K.field.toSubgroup` is Mathlib's
  subgroup `G_L` of `G_K = K.field.toSubgroup`. It is the exact body of the
  source abbreviation `CyclicCohomology.extensionSubgroup (G := G) K.field L hLK`
  (M004.002, published as the abbreviation
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup`).
- `D.extensionInertiaWithin K.field L hLK` (M012.002) is the inertia
  subgroup `I_L` of `G_K`, and
  `D.extensionNormalizedDegree K L hLK` (M012.005) is the multiplicative
  homomorphism `G_K ⧸ I_L →* ZHatMul` induced by the normalized degree
  (`ZHatMul`, M010.001, is `Multiplicative ZHat`, and `ZHat` is M008.008).
- `D.FrobeniusElements K L hLK` (M012.009) is the subtype of `G_K ⧸ I_L`
  of the elements `σ` for which there is `n : ℕ` with `0 < n` and
  `D.extensionNormalizedDegree K L hLK σ = (Multiplicative.ofAdd (1 : ZHat)) ^ n`.
- `D.frobeniusExponent K L hLK σ` (M014.012) is `Exists.choose σ.2`, the
  chosen witness `n`. It is published in the module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`,
  which is the single import here and transitively provides the other
  names.
- `Mul`, `Semigroup`, `Exists.choose_spec`, `Nat.add_pos_left`, `map_mul`,
  `pow_add`, `mul_assoc` and `Subtype.ext` are Mathlib's or Lean core's.

## Telescopes

All three declarations have the source section's implicit `G : Type*`,
which elaborates to `G : Type u_1` (source line 26; the source file has no
universe declaration), followed by `[Group G]` and `[TopologicalSpace G]`,
and then the binders below. No hypothesis is added or removed. The
normality binder is the source binder
`[hLnormal : (CyclicCohomology.extensionSubgroup (G := G) K.field L hLK).Normal]`
with `extensionSubgroup` expanded.

```lean
def frobeniusMul (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    D.FrobeniusElements K L hLK

instance frobeniusElementsMul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    Mul (D.FrobeniusElements K L hLK)

instance frobeniusElementsSemigroup (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    Semigroup (D.FrobeniusElements K L hLK)
```

## Constructions

`D.frobeniusMul K L hLK σ τ` (M015.001) is the Frobenius element whose
underlying quotient element is the product `σ.1 * τ.1`, with witness
`m + n` for the exponents `m = D.frobeniusExponent K L hLK σ` and
`n = D.frobeniusExponent K L hLK τ`. It is built in these steps.

1. As in the source, `m` and `n` are introduced by `let`.
2. Three local hypotheses are introduced, each proved by the source proof
   `(Exists.choose_spec σ.2).1` or `(Exists.choose_spec σ.2).2` of M014.013
   or M014.014 (for `τ` in the third):
   `hσpos : 0 < D.frobeniusExponent K L hLK σ` (the statement of M014.013
   for `σ`), and `hσpow` and `hτpow`, the equations
   `D.extensionNormalizedDegree K L hLK σ.1 = (Multiplicative.ofAdd (1 : ZHat)) ^ D.frobeniusExponent K L hLK σ`
   and the same for `τ` (the statement of M014.014).
3. As in the source, the value is `⟨σ.1 * τ.1, m + n, Nat.add_pos_left hσpos n, ?_⟩`,
   and the remaining equation
   `D.extensionNormalizedDegree K L hLK (σ.1 * τ.1) = (Multiplicative.ofAdd (1 : ZHat)) ^ (m + n)`
   is proved by rewriting with `map_mul`, `hσpow`, `hτpow` and `pow_add`.

Only the proofs of propositions differ in form from the source, which uses
the theorems M014.013 and M014.014 in the same positions; the underlying
element `σ.1 * τ.1` and the witness `m + n` are the source's, so by proof
irrelevance the Frobenius element is the source's.

`frobeniusElementsMul` (M015.002) is the instance `Mul` with multiplication
`D.frobeniusMul K L hLK`; the body is the source's.

`frobeniusElementsSemigroup` (M015.004) is the `Semigroup` structure whose
multiplication is the instance M015.002. Its associativity proof is the
source's: by `Subtype.ext` the claim reduces to
`(σ.1 * τ.1) * υ.1 = σ.1 * (τ.1 * υ.1)` in the quotient group, which is
`mul_assoc`.

## Modifications

Worker 5264 makes these modifications:

- Extract only M015.001, M015.002 and M015.004, with the namespaces
  `ClassFormation` (line 16) and `DegreeData` (line 24), the noncomputable
  section (line 22) and the variable declaration (line 26). Replace the
  module documentation by one describing these declarations and the
  modifications. The source `open CyclicCohomology` (line 18) is omitted;
  the source spells `CyclicCohomology.extensionSubgroup` in full, and this
  abbreviation is expanded below.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`.
- Expand `CyclicCohomology.extensionSubgroup (G := G) K.field L hLK` in the
  three normality binders (lines 31–32, 51–52 and 71–72) to its exact
  Mathlib body `L.toSubgroup.subgroupOf K.field.toSubgroup`, following the
  published sibling modules. The two expressions are definitionally equal.
- In the body of M015.001, replace the application
  `D.frobeniusExponent_pos K L hLK σ` (line 38) of M014.013 by the local
  hypothesis `hσpos`, and the rewrites with
  `D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ` and `… τ`
  (lines 40–41) of M014.014 by rewrites with the local hypotheses `hσpow`
  and `hτpow`. Each local hypothesis has the statement of the theorem it
  replaces and is proved by that theorem's source proof.
- Replace the source import `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField`
  with the published module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`.
- The declaration names, docstrings, the remaining telescopes, result types
  and the remaining bodies are unchanged.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The source theorem M015.003 `frobeniusMul_coe` is stated as a proposition
target in the sibling module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup.Statements`.
The source theorem M015.005 `extensionNormalizedDegree_frobenius_mul`
(lines 78–94) is not part of this contribution. These definitions discharge
no host class-formation, cup, transfer, Tate or reciprocity target.

## Verification

The module and its sibling modules passed a project Lean service check on
15 November 2026 with environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), with no
errors or warnings. Compilation is separate from independent semantic
acceptance and publication.

## Attribution

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
