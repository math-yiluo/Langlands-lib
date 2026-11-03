# Conditional assembly of the actual ordered-product socle

Author: Worker 864. Worker 700 updated the final assembly and audit documentation.

This supporting module is submitted with the exact proof of
`OrderedMultisegmentSocleExistence`. It proves finite length and Artinianity
of the supplied segment-socle product at positive rank, specializes the
published generic socle bridge, and transfers the published mirabolic
highest-derivative criterion to the full general-linear action. The final
adapter still assumes nontriviality, homogeneity of the actual mirabolic
restriction, and strong indecomposability of its actual highest derivative.
It does not prove the unconditional parent statement.

The lemmas retain arbitrary primes, `F : PadicField.{uF} p`, the supplied
compatible topology `T` and independent `uF,uV`. The product lemmas retain every actual
`d : T.SegmentProductDatum.{max uF uV,uF} n`. They keep the supplied blocks,
order, multiplicities and actual upper normalized induction with right
translation. No product is replaced by a selected representative.

`generalLinear_stronglyIndecomposable_of_highestDerivative` applies to any
actual smooth representation `A` of `GL_(N+1)` in carrier universe `uV`.
Its premises are nontriviality of `A`, an actual valid derivative order
`k` equal to the level of its mirabolic restriction, homogeneity of that
restriction, and strong indecomposability of its actual order-`k`
derivative. Restriction keeps the carrier, so nontriviality supplies the
same premise for the mirabolic reduction. Apply the reverse direction of
the second clause of
`Derivative.mirabolicStrongIndecomposabilityReduction.{uF,uV} F T` to
obtain strong indecomposability of the restricted action.
`stronglyIndecomposable_of_comp`, along the actual mirabolic subgroup
inclusion, then gives strong indecomposability of `A.representation`.
The proof makes no converse assertion for restriction and assumes no
exactness or classification theorem.

`segmentProduct_isFiniteLength` assumes `0 < n` and `d.HasSegmentSocles`.
For each block, the latter gives a supercuspidal representative, a proof
that it represents the segment base, and the actual irreducible-socle
relation. The first clause of that relation proves irreducibility of the
supplied block itself. Apply the published
`irreducibleProductFiniteLength.{uF,max uF uV} F T` to `d.shape` and
`d.blocks`. By the definition of `d.induced`, the result is finite length
of its actual complex group-algebra module. This argument needs no
precedence-order hypothesis and asserts no numerical length bound.

`segmentProduct_isArtinian` takes the Artinian clause of Mathlib's
`isFiniteLength_iff_isNoetherian_isArtinian`, using that finite-length
lemma for the very same group algebra and module. It retains the positive
rank and actual segment-socle block hypotheses.

`segmentProduct_socle_of_stronglyIndecomposable` works at every rank but
keeps three explicit inputs: nontriviality of `d.induced`, Artinianity of
its group-algebra module, and intrinsic strong indecomposability of its
representation. It applies the smooth clause of the published
`strongIndecomposabilitySocle` theorem at universes
`.{0,uF,0,max uF uV}`. This supplies a smooth socle in `Type (max uF uV)`
with the actual `IsIrreducibleSocle` relation. Adding the supplied
precedence-order and block-socle proofs gives `d.IsZelevinskySocle`.
The relation includes an injective intertwiner and equality of the images
of all competing irreducible embeddings in that carrier universe.

`segmentProduct_socle_of_stronglyIndecomposable_pos` assumes `0 < n` and
uses `segmentProduct_isArtinian` to discharge the preceding adapter's
Artinian premise. Its remaining product inputs are nontriviality and
strong indecomposability. Empty data and rank zero remain covered only
by the all-rank conditional adapter; this file supplies no unconditional
boundary argument. The positive-rank adapters' theorem applications use
explicit `.{uF,uV}` to avoid inferring a universe through a noninjective
`max` expression.

`segmentProduct_socle_of_highestDerivative` specializes the generic
general-linear lemma to the actual `d.induced` at rank `N+1`, with carrier
universe `max uF uV`. It then applies
`segmentProduct_socle_of_stronglyIndecomposable_pos`, using
`Nat.zero_lt_succ N` for positive rank. Its conclusion is the same actual
`d.IsZelevinskySocle π` relation, including an injection and image
uniqueness for all irreducible embeddings. Besides the supplied order
and block-socle proofs, its remaining premises are nontriviality,
`k = level` for the actual restriction, homogeneity of that restriction,
and strong indecomposability of its actual order-`k` derivative.
Homogeneity alone does not discharge the last premise. This lemma covers
every positive total rank after writing it as a successor; the all-rank
conditional bridge above still retains explicit Artinianity at rank zero.

The provenance is internal specialization of published results. The
finite-length proof is in
`Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof`;
its route embeds arbitrary irreducible products into regrouped cuspidal
induction and inherits finite length along an actual injection. The socle
bridge is in
`Langlands.Representation.Classification.StrongIndecomposabilitySocleProof`;
it uses Artinianity to obtain an atom and intrinsic strong
indecomposability to show every atom has the same image. The mirabolic
reduction is in
`Langlands.Representation.Derivative.MirabolicStrongIndecomposabilityProof`.
Its proof uses general derivative detection, the actual highest-layer
subrepresentation and its full interval order isomorphism, and the
essential-interval strong-indecomposability criterion. This adapter leaves
actual-product homogeneity and its highest-derivative premise explicit. The
paired parent proof discharges them by total-rank induction and the published
homogeneity theorem.

At Library base `538f554630aa4cd24a084e698b1768d7143ba586`, this module and
its final parent compile with zero errors and warnings in development Lake
check `bc94ac9e-c6a5-49c8-be43-47201242d78a`. Inspection of the final parent
retains independent `uF,uV` and only `propext`, `Classical.choice` and
`Quot.sound`. The complete unapplied-parent check and transitive declaration
audit also pass. These checks supply development evidence; independent
acceptance and publication apply to the submitted exact parent proof.

The [parent proof documentation](OrderedMultisegmentSocleExistenceProof.md)
records the complete 1,248-module published import inventory and fingerprints,
independently accepted proof inputs, permitted generic infrastructure and
mathematical exclusions. All imported pairs match that public base. In
particular the generic socle bridge uses an actual atom of the Artinian
subrepresentation lattice, the finite-length theorem uses the supplied
normalized product, and the exact mirabolic reduction uses the BZ77-only
detection proof and the actual highest-layer lattice equivalence. No excluded
classification or exhaustion conclusion discharges any premise here.
