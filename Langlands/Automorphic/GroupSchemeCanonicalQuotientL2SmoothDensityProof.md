# Specialization of smooth-vector density to the canonical adelic quotient

`Langlands.Global.RestrictionSplitCentre.canonicalQuotientL2SmoothDensity`
proves
`Langlands.Global.RestrictionSplitCentre.CanonicalQuotientL2SmoothDensityStatement`
from `Langlands.Automorphic.GroupSchemeCanonicalQuotientL2SmoothDensityStatement`;
its type is exactly that proposition. For a connected reductive group
scheme \(G\) over a number field \(F\) (in universe zero), it shows, for the
canonical measure `canonicalMeasure F G` on
`CanonicalQuotient F G` \(=[G]\) and the right actions on its \(L^2\)
classes:

- the vectors of \(L^2([G])\) that are real smooth for the infinite adelic
  right action `rationalQuotientL2InfiniteRightAction` are norm dense;
- the vectors of `rationalQuotientL2BiSmoothVectors`, which are real smooth
  for that action and also fixed by an open subgroup of the finite adelic
  points, are norm dense.

The right invariance supplied to these actions is
`canonicalMeasure_rightInvariant F G centralSplitTorusCharacter hG`, as in
the statement.

## Proof

The proof is one application of
`Langlands.Global.RestrictionSplitCentre.quotientL2SmoothDensity`, the proof of
`QuotientL2SmoothDensityStatement`, to the split components chosen in
`Langlands.Global.AdelicRestrictionSplitCentreCanonical`:

1. The restriction data are `canonicalRestrictionTorus F G` with
   `canonicalRestrictionComponent F G`, the chosen split component of the
   Weil restriction \(\mathrm{Res}_{F/\mathbb Q} G\). Since
   `canonicalMeasure F G` is by definition (an `abbrev`)
   `quotientHaarMeasure F G (canonicalRestrictionTorus F G)
   (canonicalRestrictionComponent F G)`, the measure in the conclusion of
   `quotientL2SmoothDensity` is the canonical one.
2. The split component of \(G\) itself is `canonicalTorus F G` with
   `canonicalComponent F G`. The theorem
   `canonicalSubgroup_eq_imageSubgroup` identifies the positive real subgroup
   of the restriction component with the positive image of this component of
   \(G\), which is the subgroup comparison hypothesis.
3. Character restriction along `canonicalComponent F G` is injective by
   `canonical_characterRestrict_injective F G centralSplitTorusCharacter hG`
   (the published proof `centralSplitTorusCharacter` of
   `CentralSplitTorusCharacterStatement`), and its range has finite index by
   `canonical_finiteIndex F G hG`, introduced as a local instance.
4. `isSplitComponent_canonicalComponent F G` shows that `canonicalComponent F G`
   is a split component; its components give centrality (`hs.1.2`) and the
   split-torus property of the source (`hs.1.1.1`).
5. Right invariance of Haar measure on the norm-one subgroup
   \(G(\mathbb A_F)^1\) is the local instance
   `AdelicGroupPoints.normOneHaarRightInvariant F G hG.smooth hG.connectedSpace`.
6. The quotient right invariance is
   `canonicalMeasure_rightInvariant F G centralSplitTorusCharacter hG`.

With these arguments the two conjuncts of `quotientL2SmoothDensity` are the
two conjuncts of the statement: the second set there,
\(\{\varphi \mid \varphi \text{ smooth at infinity and smooth for the finite
adelic action}\}\), is the carrier of `rationalQuotientL2BiSmoothVectors`, the
infimum of the archimedean smooth vectors and the finite smooth vectors, so the
two agree by definitional unfolding. The proof depends only on `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The quotient \([G]=A_G G(F)\backslash G(\mathbb A_F)\) and the subgroups
\(G(\mathbb A_F)^1\) and \(A_G\) are those of Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), §2.6, (2.19)–(2.22) and Lemma 2.6.2,
printed pp. 68–69 (PDF pp. 85–86); \(A_G\) is the identity component of the
real points of the greatest \(\mathbb Q\)-split torus in the restriction of
scalars of the centre. The registered source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`. The
density assertion is not taken from that source: it is an internal
specialization of the Library theorem `quotientL2SmoothDensity` to the
canonical choice of split components, whose hypotheses are discharged by the
character restriction, centrality and Haar invariance results named above.
