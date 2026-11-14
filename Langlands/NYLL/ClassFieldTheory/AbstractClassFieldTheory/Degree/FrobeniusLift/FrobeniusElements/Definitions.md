# NYLL M012.004, M012.005, M012.009 and M012.010: the factorized normalized degree and the Frobenius semigroup

This file adapts three definitions of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusLift.lean` at
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. It also adapts the source-private lemma
that the first definition's body uses. The original file SHA-256 is
`a0b7ac8afcc55cad383a16e6dfe093e147770a7e8f5d21c3f8843744b57b7061`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Unit | Source lines (declaration line) | Original name after `ClassFormation.DegreeData.` | Adapted name |
| --- | --- | --- | --- |
| M012.004 | 72–80 (72) | `extensionInertiaWithin_le_normalizedDegree_ker` (private) | private `Langlands.NYLL.ClassFormation.DegreeData.extensionInertiaWithin_le_normalizedDegree_ker` |
| M012.005 | 82–90 (83) | `extensionNormalizedDegree` | `Langlands.NYLL.ClassFormation.DegreeData.extensionNormalizedDegree` |
| M012.009 | 128–137 (130) | `FrobeniusElements` | `Langlands.NYLL.ClassFormation.DegreeData.FrobeniusElements` |
| M012.010 | 139–146 (140) | `frobeniusRestriction` | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusRestriction` |

## The objects

Every object is a published source definition. No replacement degree datum,
field, inertia group, normalized degree or restriction map is introduced.

- `D : DegreeData G` (M010.002) is the source degree datum. Its degree map
  takes values in `ZHatMul = Multiplicative ZHat` (M010.001).
- `K : FiniteResidueAbstractField D` (M010.021) bundles a closed subgroup
  `K.field : ClosedSubgroup G` with finiteness of its residue quotient.
- `L : ClosedSubgroup G` with `hLK : L.toSubgroup ≤ K.field.toSubgroup` is the
  extension. `L.toSubgroup.subgroupOf K.field.toSubgroup` is Mathlib's
  subgroup `G_L` of `G_K`. It is the exact body of the source's
  `extensionSubgroup K.field L hLK` (M004.002), and the published sibling
  module uses it in the same way.
- `D.extensionInertiaWithin K.field L hLK` (M012.002) is
  `G_L ⊓ D.fieldInertiaWithin K.field`, the inertia subgroup inside `G_L`,
  where `D.fieldInertiaWithin` is M010.014. It is normal when `G_L` is normal
  (instance M012.003). `D.extensionRestriction K.field L hLK` (M012.007) is
  the induced map from `G_K` modulo `extensionInertiaWithin` to `G_K / G_L`.
  All three are published in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions`.
- `D.normalizedDegree K : K.field.toSubgroup →ₜ* ZHatMul` (M011.006) is the
  normalized degree map `d_K`, published in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions`.
  Its value at `k` is
  `Multiplicative.ofAdd (zHatDivide f_K _ (D.restrictedDegreeInMulNatRange K k))`,
  where `zHatDivide` is M009.016 and `restrictedDegreeInMulNatRange` (M011.004)
  is the restricted degree with values in the image of multiplication by the
  residue degree `f_K`.

## Telescopes

All declarations have the source section's implicit `G : Type u`, with
universe variable `u` (source lines 25 and 27), followed by `[Group G]` and
`[TopologicalSpace G]`, then the explicit and instance binders below in source
order. No hypothesis is added. The normality binder
`[hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]` is the
source binder `[hLnormal : (extensionSubgroup K.field L hLK).Normal]` with
`extensionSubgroup` expanded.

```lean
private theorem extensionInertiaWithin_le_normalizedDegree_ker
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup) :
    D.extensionInertiaWithin K.field L hLK ≤
      (D.normalizedDegree K).toMonoidHom.ker

Langlands.NYLL.ClassFormation.DegreeData.extensionNormalizedDegree
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) →* ZHatMul

Langlands.NYLL.ClassFormation.DegreeData.FrobeniusElements
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] : Type u

Langlands.NYLL.ClassFormation.DegreeData.frobeniusRestriction
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    D.FrobeniusElements K L hLK →
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)
```

## Constructions

The private lemma (M012.004) keeps the source statement, but its proof is
direct instead of the source's. An element `x` of `extensionInertiaWithin`
lies in both `G_L` and `I_K`. Its second component `hx.2` says that `x` lies in
`D.fieldInertiaWithin K.field`, the kernel of the restricted degree, so
`D.degree x.1 = 1`. The published M009.017 theorem `zHatMulNat_zHatDivide`,
applied to `D.restrictedDegreeInMulNatRange K x`, gives
`f_K • (d_K x).toAdd = (D.degree x.1).toAdd`, which is therefore `0`.
`f_K • (1 : ZHatMul).toAdd` is also `0`, so the published M009.005 theorem
`zHatMulNat_injective` (multiplication by the positive natural `f_K` is
injective on `ZHat`) gives `d_K x = 1`, which means that `x` is in the kernel of
`d_K`. The source proof instead rewrites the kernel with M011.010
`normalizedDegree_ker` and then uses `hx.2`. The direct proof is the
`I_K ⊆ ker d_K` half of the source proof of M011.010, with the M011.008
identity inlined as the M009.017 term that proves it. Only the proof differs.
The statement, binders and use in M012.005 are the source's, and by proof
irrelevance the construction of M012.005 is unaffected. The lemma stays
private, as in the source. It exists only to supply the kernel condition in the
body of M012.005, and it is not a published theorem target.

`D.extensionNormalizedDegree K L hLK` (M012.005) is the source map
`d_K : G(\widetilde L|K) → ℤ̂`. It is `QuotientGroup.lift` of
`(D.normalizedDegree K).toMonoidHom` through the quotient by
`extensionInertiaWithin`, with the private lemma as the kernel condition. On
classes `QuotientGroup.mk k` it is therefore `d_K k` by definition. That
identity is the target M012.006 in the sibling Statements module.

`D.FrobeniusElements K L hLK` (M012.009) is the source semigroup
`Frob(\widetilde L|K)`. It is the subtype of classes `σ` of
`G_K / (G_L ⊓ I_K)` for which some natural number `n > 0` satisfies
`D.extensionNormalizedDegree K L hLK σ = (Multiplicative.ofAdd (1 : ZHat)) ^ n`.
Positivity of `n` is explicit, as in the source.

`D.frobeniusRestriction K L hLK` (M012.010) sends a Frobenius element `σ` to
`D.extensionRestriction K.field L hLK σ.1`, its image in `G_K / G_L`. Its
surjectivity, M012.013, is stated in the sibling module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.FrobeniusElements.Statements`.

## Modifications

Worker 5264 makes these modifications:

- Extract only M012.004, M012.005, M012.009 and M012.010, with the
  surrounding namespaces, the source's noncomputable section, universe and
  variable declarations (source lines 23, 25 and 27), and narrow the module
  documentation to these declarations. The private source definition M012.011
  and private lemma M012.012 are used only in the proof of M012.013 and are
  not part of this module.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`.
- Expand `extensionSubgroup K.field L hLK` to its exact Mathlib body
  `L.toSubgroup.subgroupOf K.field.toSubgroup` in the normality binders and in
  the result type of M012.010, following the published sibling module that
  defines `extensionInertiaWithin` and `extensionRestriction`. The two
  expressions are definitionally equal. The declaration names, docstrings,
  remaining telescopes, result types and the construction bodies of M012.005,
  M012.009 and M012.010 are unchanged.
- Replace the proof of the private lemma M012.004 (source lines 78–80,
  `intro x hx; rw [D.normalizedDegree_ker K]; exact hx.2`) by the direct
  proof described above, which uses the published M009.017 and M009.005
  theorems instead of the M011.010 theorem `normalizedDegree_ker`. Its
  statement is unchanged. This removes the dependence of M012.005 on the
  M011.010 proof, which is routed separately (Task 6601).
- Replace the source import `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius`
  with three published modules:
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions`
  contains `extensionInertiaWithin`, its normality instance and
  `extensionRestriction`;
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions`
  contains `restrictedDegreeInMulNatRange` and `normalizedDegree`;
  `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U017.Proofs`
  contains the M009.017 theorem `zHatMulNat_zHatDivide`, and it transitively
  imports M009.005 `zHatMulNat_injective`.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
