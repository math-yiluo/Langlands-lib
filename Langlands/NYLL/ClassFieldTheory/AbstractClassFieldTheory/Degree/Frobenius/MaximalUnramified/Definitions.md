# NYLL M011.012 and M011.014: the maximal-unramified degree equivalence and the Frobenius

This file adapts two definitions of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean` at
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, with the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Unit | Source lines (docstring, declaration) | Original name after `ClassFormation.DegreeData.` | Adapted name |
| --- | --- | --- | --- |
| M011.012 | 167, 168–192 | `maximalUnramifiedDegreeEquiv` | `Langlands.NYLL.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv` |
| M011.014 | 202–203, 204–207 | `frobenius` | `Langlands.NYLL.ClassFormation.DegreeData.frobenius` |

The source-private theorem M011.011
`fieldInertiaWithin_le_normalizedDegree_ker` (source lines 162–165) is used
only in the body of M011.012. It is not a separate declaration here; see
Modifications.

## The objects

Every object is a published source definition or theorem. No replacement
degree datum, field, inertia group or normalized degree is introduced.

- `D : DegreeData G` (M010.002) is the source degree datum: a continuous
  surjective homomorphism `D.degree : G →ₜ* ZHatMul`, where
  `ZHatMul = Multiplicative ZHat` (M010.001).
- `K : FiniteResidueAbstractField D` (M010.021) bundles a closed subgroup
  `K.field : ClosedSubgroup G` (Mathlib's `ClosedSubgroup`) with finiteness of
  its residue quotient. `K.field.toSubgroup` is the group `G_K`, and
  `K.residueDegree` is its positive residue degree `f_K`.
- `D.fieldInertiaWithin K.field : Subgroup K.field.toSubgroup` (M010.014) is
  the inertia group `I_K`, the kernel of the degree map restricted to `G_K`.
  It is normal by the published instance `fieldInertiaWithin_normal`. Both are
  in `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`.
- `D.normalizedDegree K : K.field.toSubgroup →ₜ* ZHatMul` (M011.006) is the
  normalized degree map `d_K = (1/f_K) d` on `G_K`, published in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions`.
- The published M011.009 theorem `normalizedDegree_surjective D K` concludes
  `normalizedDegree_surjectiveStatement D K`, which unfolds to
  `Function.Surjective (D.normalizedDegree K)`. It is in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U009.Proofs`.
- The published M011.010 theorem `normalizedDegree_ker D K` concludes
  `normalizedDegree_kerStatement D K`, which unfolds to
  `(D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field`.
  It is in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs`.

## Telescopes

Both declarations have the source section's implicit binder `{G : Type*}`
(one universe parameter) followed by `[Group G]` and `[TopologicalSpace G]`
(source line 23), and then the explicit binders below. No hypothesis is added.

```lean
def maximalUnramifiedDegreeEquiv (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) ≃* ZHatMul

def frobenius (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field
```

## Constructions

`D.maximalUnramifiedDegreeEquiv K` (M011.012) is the isomorphism
`d_K : G(\widetilde K|K) = G_K / I_K ≃ ℤ̂`. The construction is the source's.
Because `I_K` is contained in the kernel of `d_K`, the normalized degree
descends to a homomorphism `dquot : G_K / I_K →* ZHatMul` by
`QuotientGroup.lift`. The equivalence is `MulEquiv.ofBijective dquot`.

- Injectivity: if `dquot a = dquot b` for representatives `a b ∈ G_K`, then
  `d_K (a⁻¹ * b) = (d_K a)⁻¹ * d_K b = 1`. So `a⁻¹ * b` lies in the kernel of
  `d_K`, which is `I_K` by M011.010, and `a` and `b` have the same class.
- Surjectivity: `d_K` is surjective (M011.009), so its lift through the
  quotient is surjective (`QuotientGroup.lift_surjective_of_surjective`).

`D.frobenius K` (M011.014) is the Frobenius class `φ_K ∈ G_K / I_K`, the
preimage of the generator `Multiplicative.ofAdd 1` under the equivalence:
`(D.maximalUnramifiedDegreeEquiv K).symm (Multiplicative.ofAdd (1 : ZHat))`.
It is characterized by `d_K(φ_K) = 1`. The body is the source's.

## Modifications

Worker 5264 makes these modifications:

- Extract only M011.012 and M011.014, with the namespaces
  `ClassFormation` (line 17) and `DegreeData` (line 25), the noncomputable
  section (line 21) and the variable declaration (line 23). Narrow the module
  documentation to these declarations. The source file has no `open` and no
  `universe` declaration.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`.
- Do not add the source-private theorem M011.011. Its statement is
  `D.fieldInertiaWithin K.field ≤ (D.normalizedDegree K).toMonoidHom.ker`,
  and its source proof is `rw [D.normalizedDegree_ker K]`. In the body of
  M011.012, before `let dquot`, add two local hypotheses:
  `hker : (D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field`,
  proved by the published M011.010 theorem `D.normalizedDegree_ker K`, whose
  `Statement` proposition unfolds by definition to this equation; and
  `hle`, with exactly the statement of M011.011, proved by `rw [hker]`, which
  is the source proof of M011.011. The two source uses
  `(D.fieldInertiaWithin_le_normalizedDegree_ker K)` (source lines 174 and
  192) become `hle`.
- In the injectivity proof of M011.012, the source rewrite
  `rw [← D.normalizedDegree_ker K]` (source line 182) becomes
  `rw [← hker]`, which rewrites with the same equation.
- These changes affect only proofs of propositions inside the construction.
  The quotient map, the lifted homomorphism and the equivalence are the
  source's, so `maximalUnramifiedDegreeEquiv` and `frobenius` have the source
  values and types.
- Replace the source import `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields`
  with the two published modules
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U009.Proofs`
  and
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs`.
  They contain the M011.009 and M011.010 theorems and transitively import
  `DegreeData`, `FiniteResidueAbstractField`, `fieldInertiaWithin`, its
  normality instance, `ZHatMul` and `normalizedDegree`.
- The declaration names, docstrings, telescopes and result types are
  unchanged.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The source theorems `maximalUnramifiedDegreeEquiv_mk` (M011.013) and
`maximalUnramifiedDegreeEquiv_frobenius` (M011.015) between and after these
definitions are not part of this contribution. These definitions discharge no
host class-formation, cup, transfer, Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 14 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Declaration inspection of `frobenius` reported one universe parameter and
the axioms `propext`, `Classical.choice` and `Quot.sound`. Compilation is
separate from independent semantic acceptance and publication.

## Attribution

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
