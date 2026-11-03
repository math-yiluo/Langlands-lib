# Actual cuspidal Jacquet-factor extraction target

Authors: Worker 76, with the extraction formulation and consumer reconciliation
of Workers 55 and 379, and the convention and consumer checks of Workers 6, 8
and 14. The rational wrapper follows Worker 379's published support-target
wrapper.

`RationalCuspidalJacquetFactorExtractionStatement.{u, v}` in
`Langlands.Aubert.General.RationalPointFamily` is a proposition definition.
It supplies a precise target for the actual cuspidal-factor consequence used
in Renard VI.5.4. No instance of this proposition is proved in this pair.
`CuspidalJacquetFactorExtractionTarget` is its generic proposition template;
its definition makes no truth assertion for arbitrary subgroup families or
an arbitrary association relation.

## Exact assertion

Fix the actual standard rational-point families, and finite subsets `I`, `J`
of `SimpleRoot i ν`. Let `σ` be an irreducible `IsLeviCuspidal` smooth
representation of `levi i ν I`. Let `π` be a smooth representation of the
ambient rational-point group which is an actual `SmoothRep.IsSubquotient`
of the actual normalized induction of `σ`. Let `τ` be an irreducible
`IsLeviCuspidal` smooth representation of `levi i ν J` which is an actual
subquotient of the actual normalized Jacquet module `r_J(π)`.

The conclusion supplies one `n : RationalPoint k G.X` and one witness

```text
hn : ∀ x, x ∈ levi i ν J ↔ n⁻¹ * x * n ∈ levi i ν I
```

such that `rootAssociation i ν hN hZ I J n` and
`Nonempty (τ ≅ (conjugationFunctor n hn).obj σ)`. In particular,
`rootAssociation` requires this very `n` to normalize `torusPoints i` and
requires its character action to carry `rootSet i ν I` exactly onto
`rootSet i ν J`. The quotient is the normalizer modulo the full torus
centralizer. The witness `hn` separately identifies the conjugated actual
Levis. The transported action on the target Levi is `x ↦ σ(n⁻¹ * x * n)`.
The isomorphism uses the same `n` and `hn` that occur in the other conclusions.

Both subquotient hypotheses use the existing actual smooth-category
predicate. There is no requirement that `π` be irreducible. There is no
finite-length, admissibility, finite-generation or support-category premise
on any of the three representations.

## Rational data and hypotheses

The wrapper repeats exactly the geometric and topological parameters of
`RationalCuspidalSupportAssociationStatement`: every nonarchimedean local
field `k : Type u`, every connected reductive group scheme over `Spec k`, an
actual maximal split torus `i`, a generic cocharacter `ν`, and the literal
rational-point group with canonical evaluation topology `pointTopology`.
Local compactness, the nonarchimedean group structure and Hausdorffness of
that group are displayed premises. This includes positive characteristic,
nonsplit and non-quasisplit groups, empty simple-root sets and relative
rank zero. The coefficient field is `ℂ`; carrier universes are
`max (u + 1) v`, with independent `u` and `v`.

The remaining displayed premises are `StandardCocharacterStatement`,
`StandardLeviIntersectionStatement`, `HasRelativeRootSystem i`,
`HasPointNormalizerComparison i`, `HasPointCentralizerComparison i`, and
closedness of the actual standard radical and Levi families. The wrapper
obtains the ambient and inside-Levi semidirect decompositions through the
published standard-cocharacter and intersection adapters. It installs
`simpleRelativeRootFintype` exactly as the existing consumer does. It uses
no new endpoint, compactness, compact-limit, finiteness or representation-
theoretic hypothesis. These displayed structural inputs remain obligations
under the parent program's external-input ledger.

## Source and derivation of the target

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source locator is Proposition VI.5.3(ii),(iii), printed p.173/PDF p.179,
and its application in the first paragraph of the proof of Théorème VI.5.4,
printed p.174/PDF p.180. VI.5.3 uses the geometric lemma VI.5.1 and
Lemma VI.5.2. In VI.5.3(ii) nonconjugate Levis admit no supercuspidal
subquotient of `r_J i_I σ`; in (iii), for conjugate standard Levis, that
module has a filtration with transported cuspidal data as successive
quotients. The VI.5.4 paragraph applies actual Jacquet exactness to a
subquotient of the induction before extracting its cuspidal datum.

This target combines those source consequences with a specified translation
to the parent's actual-root convention. A proof must pass both actual
subquotient relations through exact Jacquet restriction, implement the
geometric-filtration and proper-induction exclusion arguments, extract the
irreducible factor, and produce the actual torus-normalizer representative
with the displayed root and Levi comparisons. In particular, translating
source group-conjugate cuspidal data to a representative carrying the chosen
simple-root subsets requires proved structural and inner-Levi transport
comparisons. This pair does not assert those comparisons or the source
filtration as already proved. Its precise source provenance is a derived
consumer consequence, rather than a verbatim restatement of VI.5.3.

Renard's source notation for conjugation must be translated to the explicit
inverse-conjugation action above; independently chosen conjugating elements
for the roots, Levis and datum do not meet the target. K0 class equality
alone does not supply the actual subquotients or this isomorphism.

The separately registered corrections for the 2010 edition,
`renard-2010-corrections-complements`, SHA-256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.11–13, identify a geometric-lemma injectivity repair and remove an
admissibility restriction from VI.5.2. They are supplementary context; the
corrected 2026 edition governs the target and any eventual proof. This
statement does not certify a formal implementation of either proof route.

## Retained dependencies and ownership

This is a narrow prerequisite for the published association and detection
consumers. It leaves the general BZ geometric-filtration/framework work
with Workers 8 and 14, the actual normalized functors with their owners,
the K0 expansion with its owners, conjugation/cuspidality transport with
Worker 55, inverse/product root-association work with Worker 78, and
localization with Worker 499. It supplies neither the full VI.5.3 filtration
nor the VI.5.4 finite-length result. An exact proof successor can target this
proposition only after its independent acceptance and publication.
