# NYLL M014.016 and M014.020: the continuous factorized normalized degree and its kernel restriction

This file adapts two definitions of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, with the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Unit | Source lines (docstring, declaration) | Original name after `ClassFormation.DegreeData.` | Adapted name |
| --- | --- | --- | --- |
| M014.016 | 344, 345–357 | `extensionNormalizedDegreeContinuous` | `Langlands.NYLL.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous` |
| M014.020 | 392–393, 394–401 | `extensionDegreeKernelRestriction` | `Langlands.NYLL.ClassFormation.DegreeData.extensionDegreeKernelRestriction` |

## The objects

Every object is a published source definition or theorem. No replacement
degree datum, field, inertia group, normalized degree, restriction map or
quotient lift is introduced.

- `D : DegreeData G` (M010.002) is the source degree datum, with values in
  `ZHatMul = Multiplicative ZHat` (M010.001).
- `K : FiniteResidueAbstractField D` (M010.021) bundles a closed subgroup
  `K.field : ClosedSubgroup G` with finiteness of its residue quotient;
  `K.field.toSubgroup` is the group `G_K`.
- `L : ClosedSubgroup G` with `hLK : L.toSubgroup ≤ K.field.toSubgroup` is the
  extension. `L.toSubgroup.subgroupOf K.field.toSubgroup` is Mathlib's
  subgroup `G_L` of `G_K`. It is the exact body of the source's
  `extensionSubgroup K.field L hLK` (M004.002), and the published sibling
  modules use it in the same way.
- `D.extensionInertiaWithin K.field L hLK` (M012.002) is
  `G_L ⊓ D.fieldInertiaWithin K.field`, the inertia subgroup inside `G_L`,
  where `D.fieldInertiaWithin K.field` (M010.014) is the inertia group `I_K`.
  It is normal when `G_L` is normal (instance M012.003).
  `D.extensionRestriction K.field L hLK` (M012.007) is the induced
  homomorphism from `G(\widetilde L|K) = G_K / extensionInertiaWithin` to
  `G(L|K) = G_K / G_L`. These are published in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions`.
- `D.normalizedDegree K : K.field.toSubgroup →ₜ* ZHatMul` (M011.006) is the
  continuous normalized degree map `d_K`.
  `D.extensionNormalizedDegree K L hLK` (M012.005) is the homomorphism
  `G(\widetilde L|K) →* ZHatMul` induced by `d_K` through the quotient by
  `extensionInertiaWithin`, published in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.FrobeniusElements.Definitions`.
- `Langlands.NYLL.PortInternal.M014.d002` (M014.002) is the published public
  name of the source-private helper `continuousQuotientLift`: for a normal
  subgroup `N` of a topological group `A` and `f : A →ₜ* B` with
  `N ≤ f.toMonoidHom.ker`, it is `QuotientGroup.lift N f.toMonoidHom hN` as a
  continuous homomorphism `A ⧸ N →ₜ* B`. It is published in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.U002.Definitions`.
- The published M011.010 theorem `normalizedDegree_ker D K` concludes
  `normalizedDegree_kerStatement D K`, which unfolds to
  `(D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field`.
  It is in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs`.

## Telescopes

Both declarations have the source section's implicit `G : Type u`, with the
universe variable `u` (source lines 27 and 29), followed by `[Group G]` and
`[TopologicalSpace G]`, and then the explicit and instance binders below. No
hypothesis is added. The normality binder
`[hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]` is the
source binder `[hLnormal : (extensionSubgroup K.field L hLK).Normal]` with
`extensionSubgroup` expanded.

```lean
def extensionNormalizedDegreeContinuous (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) →ₜ* ZHatMul

def extensionDegreeKernelRestriction (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker →*
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)
```

## Constructions

`D.extensionNormalizedDegreeContinuous K L hLK` (M014.016) is the factorized
normalized degree `d_K : G(\widetilde L|K) → ℤ̂` as a continuous
homomorphism. Its underlying monoid homomorphism is
`D.extensionNormalizedDegree K L hLK` (M012.005). Its continuity field is the
continuity field of `PortInternal.M014.d002` applied to the normal subgroup
`extensionInertiaWithin`, the continuous map `d_K` on `G_K`, and the
containment of `extensionInertiaWithin` in the kernel of `d_K`. That
containment holds because an element of `extensionInertiaWithin = G_L ⊓ I_K`
lies in `I_K` (the second component `hx.2`), and `I_K` is the kernel of `d_K`
by M011.010. The quotient carries Mathlib's quotient topology.

`D.extensionDegreeKernelRestriction K L hLK` (M014.020) restricts
`extensionRestriction : G(\widetilde L|K) → G(L|K)` to the kernel of
`extensionNormalizedDegreeContinuous`. It is the composition of
`extensionRestriction` with the inclusion of that kernel. The body is the
source's.

## Modifications

Worker 5264 makes these modifications:

- Extract only M014.016 and M014.020, with the namespaces `ClassFormation`
  (line 19) and `DegreeData` (line 300), the noncomputable section (line 25),
  the universe declaration (line 27) and the variable declaration (line 29).
  Narrow the module documentation to these declarations. The source
  `open CyclicCohomology` (line 21) is omitted: in the extracted
  declarations it serves only to resolve `extensionSubgroup`, which is
  expanded below.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`.
- Expand `extensionSubgroup K.field L hLK` to its exact Mathlib body
  `L.toSubgroup.subgroupOf K.field.toSubgroup` in both normality binders and
  in the result type of M014.020, following the published sibling modules.
  The two expressions are definitionally equal.
- In the body of M014.016, the source-private helper `continuousQuotientLift`
  (M014.002) is its published public name
  `Langlands.NYLL.PortInternal.M014.d002`, which has the source signature and
  body.
- In the kernel-containment proof inside M014.016, the source rewrite
  `rw [D.normalizedDegree_ker K]` (source line 356) becomes a local
  hypothesis `hker : (D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field`,
  proved by the published M011.010 theorem `D.normalizedDegree_ker K`, whose
  `Statement` proposition unfolds by definition to this equation, followed by
  `rw [hker]`. The rest of that proof, `intro x hx` and `exact hx.2`, is the
  source's. The change affects only the proof of a proposition, so the
  continuous homomorphism is the source's.
- Replace the source imports `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift`,
  `Nyll.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration` and
  `Nyll.GaloisCohomology.Topology.TotallyDisconnectedQuotients` with three
  published modules:
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.FrobeniusElements.Definitions`
  contains `extensionNormalizedDegree` and transitively imports
  `extensionInertiaWithin`, its normality instance, `extensionRestriction`
  and `normalizedDegree`;
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.U002.Definitions`
  contains `PortInternal.M014.d002`;
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs`
  contains the M011.010 theorem.
- The declaration names, docstrings, remaining telescopes and result types,
  and the body of M014.020 are unchanged.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The source theorems M014.017 `extensionNormalizedDegreeContinuous_apply`,
M014.019 `extensionNormalizedDegreeContinuous_surjective` and M014.021
`extensionDegreeKernelRestriction_injective` are stated as proposition
targets in the sibling module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.NormalizedDegreeContinuous.Statements`.
The source theorem M014.018 `extensionNormalizedDegreeContinuous_toMonoidHom`
is not part of this contribution. These definitions discharge no host
class-formation, cup, transfer, Tate or reciprocity target.

## Verification

The module and its sibling Statements module passed a project Lean service
check on 14 November 2026 with environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
