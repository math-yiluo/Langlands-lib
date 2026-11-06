# Compact quotient comparison for arbitrary represented parabolics

This internal construction specializes the published split-stages compact
quotient comparison to the literal point images of an arbitrary represented
parabolic `q`, its rational Levi `l`, and its geometric unipotent radical `r`.
The ambient affine point group has its canonical topology and is locally
compact and nonarchimedean over a Hausdorff nonarchimedean local field.
The multiplication map of the Levi and radical is an isomorphism.

Write `Q₀ = pointImage q`, `L₀ = pointImage (l ≫ q)`, and let `π : Q₀ → L₀`
be the actual semidirect projection, with section `s` the literal inclusion.
The intermediate subgroup `S` and coefficient subgroup `H` are explicit closed
subgroups of `Q₀`. The comparison requires `π.ker ≤ S`, `H ≤ S`, and that the
section sends every element of `S.comap s` into `H`. These are explicit
hypotheses of this intermediate construction. It does not derive them from an
orbit or add them to the published closed local statement.

The nested retraction is `rS = splitStagesRetraction π s hrs S hker`, its
section is `sS = s.subgroupComap S`, and its coefficient subgroup is
`HS = H.subgroupOf S`. The intersection used in integration is exactly
`I = HS.comap rS.ker.subtype`. The map `φ : HS → H` removes the intermediate
subtype using `H ≤ S`.

`representedProjectionKernelRadicalEquiv` identifies the actual
Levi-projection kernel homeomorphically with the original radical point image.
`representedNestedKernelRadicalEquiv` removes the further intermediate
subgroup, giving the same radical with its inherited topology. Local
compactness follows from closedness of the actual radical image.

Every compact subset of this radical lies in a compact subgroup by the
published `LeviRadicalCompactSubgroups` theorem. A compact open subgroup at the
identity, together with any specified element, lies in one such compact
subgroup. That subgroup is open because it contains the original identity
neighborhood. Transport gives a compact open cover of the nested kernel.
Compact open bases for the nested kernel and `Q₀` follow from the published
nonarchimedean neighborhood-basis theorem.

Every regular left Haar measure on the nested kernel and on each closed
subgroup is consequently right invariant by
`Haar.compactOpenCoverUnimodularity`. In `representedNested_measureExists`,
choose the canonical Haar measures on the kernel and its actual closed
intersection `I`. The existing quotient-measure existence theorem supplies a
compatible quotient measure finite on compact sets. All measurable spaces in
this step are the Borel spaces of the inherited topologies.

`representedCompactComparisonFamily` is the type of natural families, for
all smooth complex representations `A` of `H`, of representation equivalences
from

`((compactInduced H A.representation).toCoinvariants π.ker).comp s`

to compact induction from `S.comap s` of the literal coefficient

`twist (Jacquet.complexCharacter (splitKernelHaarRatio rS sS HS hSI hHSc))
  (splitKernelCoefficientAction rS sS HS hSI (A.representation.comp φ))`.

Here `hSI` is the supplied section condition after subtype removal, and
`hHSc` is the closedness of `HS` inherited from `H`. The scalar is exactly the
published split-kernel Haar ratio; it has not been identified with a source or
target normalized parabolic character. The family also contains the equality
expressing naturality for every smooth coefficient morphism, using the actual
compact-induction map, normal-coinvariant map, and
`splitStagesCoefficientMap`. Group and coefficient universes are independent.

`representedCompactComparison_nonempty` chooses one common system of quotient
measures from the existence theorem, applies `splitStagesCompactEquiv` to every
smooth coefficient, and uses `splitStagesCompactEquiv_natural` for all
morphisms. Projection continuity comes from the original represented
parabolic theorem; section continuity is inherited from the subtype
inclusions. `representedCompactComparison` then chooses a member of this
nonempty type. Neither a measure choice nor a Haar-invariance premise is an
external hypothesis of this construction.

This is a derived internal adapter of the existing split-stages integration
and actual-radical compact-subgroup results. Full stabilizer containment,
the source-radical image, the source coefficient quotient identification, and
the final normalization identity remain separate obligations for the
represented geometric lemma. This module does not prove the closed local
orbit-comparison statement.
