# Recognition invariance for net selections of original charts

This module constructs the same-space subatlas determined by any selected
family of original charts which forms a net. It constructs its coherent
strong quasi-isomorphism to the original presentation and derives
recognition invariance, actual affinoid diagram comparisons and an actual
strong isomorphism after full recognition.

The construction does not require the selection to locally refine every
original chart. Its only selection hypothesis is a net law on the selected
original chart domains. The local refinement construction remains a
sufficient special case.

## Source and scope

The registered original is Vladimir G. Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), literature identifier
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant passages are the net definition in §1.1, printed pp.13–14 /
PDF pp.10–11; Definition 1.2.3, printed p.16 / PDF p.13; Definitions 1.2.7
and 1.2.9, printed pp.18–19 / PDF pp.15–16; the subnet discussion, printed
p.20 / PDF p.17; and Proposition 1.2.13, printed p.21 / PDF p.18.

Berkovich's subnet notation allows a family contained in the local-domain
enlargement of the original net, denoted by a bar. This module treats the
special case of a net selected from the original charts themselves. It
does not claim the full local-domain subnet statement or maximal-atlas
uniqueness. The source notation on PDF pp.17–18 was checked against
rendered pages.

The implementation is a derived construction. It inherits the original
atlas restrictions and their universal properties and uses the existing
general coherent-quasi-isomorphism recognition results. The input net
law concerns the original chart domains; recognition invariance, an
affinoid comparison or a strong inverse is not supplied as an assumption.

## Input and selected atlas

Let `K` be a complete normed field with ultrametric distance and let `A`
be an actual `AffinoidAtlasPresentation.{u,v,w} K`. In particular, its
algebras are actual finite positive-polyradius presented affinoid
algebras, its spectrum charts are embeddings, its chart domains form a
net, and its bounded restrictions have the complete affinoid-domain
factorization property.

For a predicate `P` on the original indices,
`IndexedAffinoidAtlas.IsNetSelection P` is the proposition that
`selectedChartFamily P` is a net on the original space. It contains no
condition about recognized subsets. Given its proof `hP`,
`netSubatlas P hP` has subtype indices `{i // P i}` and exactly the
original algebra, chart and restriction at each selected index. It
inherits local Hausdorffness, chart-domain injectivity, all restriction
identities and the complete restriction universal property. The supplied
net law is precisely its required net field.

`isNetSelection_of_locallyRefining` obtains this input law from the
previous relative local refinement hypothesis.
`netSubatlas_eq_subatlas` identifies the resulting actual atlas with
the previous construction; no choices of new algebras are involved.
`netSubpresentation` retains `A.space` definitionally.

## Strong inclusion and its laws

`StrongHom.restrictNetSubatlasSource` restricts an arbitrary strong map
to the selected source indices, retaining its ambient map and every
admissible bounded pullback. A supplied full quasi-isomorphism property
and a supplied intrinsic pullback coherence law are inherited simply
by evaluating the original laws at the underlying selected index.

`strongNetSubatlasInclusion` applies that construction to the original
strong identity. Its ambient map is the continuous identity. At every
admissible selected index `i` and original target index `j`, its bounded
pullback is the original restriction from `j` to `i.val`, including when
`j` is not selected.

`isQuasiIso_strongNetSubatlasInclusion` uses the identity homeomorphism
and the original restrictions' full domain representations. This
representation includes closedness, the exact spectrum image, and unique
bounded factorization after every presented-affinoid coefficient test.
`strongNetSubatlasInclusion_hasCoherentPullbacks` restricts the proved
original identity coherence. Thus coherence is constructed here rather
than required as another hypothesis on the selected family.

## Recognition and actual algebra comparisons

`netSubatlasRecognitionEquivalence` specializes
`generalRecognizedImageEquivalence` to this concrete inclusion. Its
forward functor goes from the selected recognized inclusion category to
the original one. Its reverse is constructed through recognition
iteration and idempotence, as in the general result. The forward image
and reverse preimage formulas both simplify to the unchanged literal
subset because the ambient map is the identity. The two locus lemmas
record these facts.

`netSubatlas_recognizedAffinoidFamily` then proves literal equality of
the two complete recognized families as sets of subsets of `A.space`.
It follows from the general image-family equality by simplifying both
identity images.

`netSubatlasRecognitionAffinoidNatIso` and
`netSubatlasReverseRecognitionAffinoidNatIso` specialize the actual
forward and reverse affinoid diagram comparisons along this equivalence.
The diagrams take values in the opposite category of actual presented
affinoid algebras and complete bounded algebra maps. Their natural
isomorphisms therefore retain bounded mutually inverse maps and
naturality of the full restrictions, including information invisible to
spectrum points. These constructions use the general results directly;
no equality of bounded maps is inferred from equality of point maps.

## Actual strong isomorphism after full recognition

`netSubatlasFullRecognitionStrongIso` specializes
`fullRecognitionStrongIso`. It is an isomorphism between the full
recognition presentations of the selected and original atlases in
`SaturatedAtlasPresentation.{u,v,v} K`, whose arrows are actual strong
maps and whose composition is the constructed saturated composition.
It retains every admissible bounded pullback and both complete strong
inverse identities. Its forward map is the general full-recognition
extension and its inverse is the constructed reverse map, rather than
a formal inverse in a localization category.

The forward ambient map is definitionally the identity. The reverse
ambient map is the identity by the proved original ambient inverse law.
No identification of the chosen recognized algebras as equal objects is
asserted.

## Remaining scope

Neither original full-domain closure, directedness nor upper cofinality
is assumed. Local Hausdorffness is inherited from the actual atlas
data; global Hausdorffness is not added. There is no extra nontrivial
valuation, reducedness or nonemptiness premise.

The general subnet statement involving charts of the local-domain
enlargement, arbitrary equivalent nets, maximal-atlas uniqueness,
unrestricted analytic morphism identification, analytic étale and
quasi-étale sites and the Harris specializations remain further work.
