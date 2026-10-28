# Character localization of compact induction in p-adic unipotent groups

Worker 672 proves the published proposition
`Langlands.Whittaker.CompactLocalizationStatement.{uF,uV}` by the closed theorem
`Langlands.Whittaker.compactLocalization` in
`Langlands.Representation.Whittaker.CompactLocalizationProof`. The field and
coefficient universes are independent, and the theorem has no additional
parameters or hypotheses. The target pair and all its imports are unchanged.

For the canonical p-adic upper-unipotent group of rank `n + 1`, every closed
subgroup `H`, every smooth complex representation `σ` on an arbitrary module,
and every smooth ambient character `θ`, the conclusion is a full complex linear
equivalence between the actual character quotient of `compactInduced H σ` and
that of `σ` for the restricted character. It includes rank one and the trivial
character. The quotient uses the positive-character relations
`ρ(g)v - θ(g) • v`, and compact induction uses the existing right-translation
action. No normalization or naturality of the resulting equivalence is asserted.

## Character transport

The private lemma `coinvariantKer_top` identifies ordinary relations after
restriction to the full subgroup with the original ordinary relation submodule.
`characterRelations_top` combines this with the published
`Jacquet.Localization.relations_eq_twisted_ker`: the positive-character relation
span equals the ordinary relation submodule for the inverse-character twist.
The quotient equivalence `characterCoinvariantsEquiv` is the identity on
representatives, implemented with `Submodule.quotEquivOfEq`.

The private `coinvariantsEquiv` descends a representation equivalence and its
inverse using Mathlib's actual coinvariant maps. Quotient-map extensionality
and the inverse identities prove that the two descended maps are inverse.

The helper `inverseSmoothCharacter` retains openness of the character kernel
under inversion. `compactLocalizationOfOrdinary` composes the source character
comparison, the published `Induction.compactInductionTwistEquiv` for this inverse
character, an ordinary coinvariant equivalence, and the inverse target character
comparison. This gives exactly the two quotients in the target. In particular,
the character used to twist the inducing representation is
`(θ.toMonoidHom.comp H.subtype)⁻¹`.

## The actual ordinary integral

The private `compactLocalizationOfCompatible` works with regular two-sided Haar
measures on a locally compact Hausdorff group and its closed subgroup, and with
a compatible quotient measure finite on compact sets. It proves smoothness of
the inverse-character inducing twist: the restricted inverse character has open
kernel by continuity of the subtype inclusion, and `isSmooth_twist_iff` applies.

It then imports and applies
`Induction.compactCoinvariantIntegralBijective.{uG,uV}` from
`Langlands.Representation.Induction.CompactCoinvariantBijectivityProof`,
authored by Worker 199. `LinearEquiv.ofBijective` is applied to the actual
`Induction.compactCoinvariantDesc`, using the compatible measure's proved right
invariance. The helper transports this integral equivalence through the character
comparisons above. The normalized-section and spanning argument establishing
ordinary bijectivity is imported without copying its proof.

## Canonical p-adic specialization and measures

The public theorem installs the target's canonical field topology and
general-linear topological group structure. It uses the published canonical
Hausdorff and locally compact structures on the actual upper-unipotent subgroup
`U`, together with two distinct compact-open facts:

- `F.canonicalUpperUnipotentCompactOpen` gives a compact open subgroup inside
  each open identity neighborhood, as needed by ordinary integral bijectivity.
- `RankinSelberg.unipotent_exists_compact_open`, with the canonical valued-field
  and local-field instances, puts each element of `U` inside a compact open
  subgroup, as needed for Haar right invariance.

Closedness gives local compactness of `H`. The proof equips `U`, `H` and the
actual left-coset quotient with their Borel measurable structures, and chooses
Mathlib's regular left Haar measures `μU` and `μH`.

The imported closed theorem `Haar.compactOpenCoverUnimodularity` from
`Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof`, authored by
Worker 117, supplies right invariance of both chosen measures. Its ambient
argument uses regular Haar uniqueness and cancellation of the finite nonzero
mass of a compact open subgroup containing the translated element. Its
closed-subgroup clause derives the requisite cover by pulling back compact open
subgroups along the closed subtype embedding. The published proof credits
Worker 103's ambient route and Worker 672's closed-subgroup route; this consumer
imports the result without duplicating it.

`QuotientIntegration.compatibleMeasureExists` now supplies a compatible measure
on the actual left quotient. Its regularity supplies finiteness on compact sets.
The private integral-and-character assembly finishes the equivalence. Thus all
measure, right-invariance and bijectivity hypotheses occur only in private
helpers and are discharged in the closed public theorem.

## Original source and provenance

This is an internal derived specialization of I. N. Bernstein and A. V.
Zelevinsky, *Induced representations of reductive p-adic groups I*, Ann. Sci.
ENS (4) **10** (1977), 441–472, §§1.7–1.9 and 5.17. Registered source:
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The cited sections were read at PDF pages 4–6 and 27–28 (printed pp.443–445 and
466–467). The retained source is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

Section 5.17 weights the integral by the inverse character and reduces to the
ordinary character using the inverse twist. That sign agrees with the actual
positive-character relations used here. The implemented Lean proof reuses the
Library's relation comparison, induction twist, ordinary integral bijectivity,
Haar invariance and quotient-measure existence proofs. The canonical p-adic
matrix formulation, arbitrary closed-subgroup scope, independent universes and
measure-free closed telescope are the published target's derived formulation.
No original proof text is copied.
