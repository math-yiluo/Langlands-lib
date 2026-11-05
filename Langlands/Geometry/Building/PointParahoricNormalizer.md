# Actual normalizer intersections at points and chambers

This derived construction concerns the existing sharp fixers, generated full
parahorics, normalizer action and centralizer-zero subgroup. All field data have
arbitrary universe `u`. Opposite factor pairs remain explicit through
`RelativeRoot.HasRankOneFactorization`.

For valuation building data satisfying the apartment axioms, a normalizer element
in the singleton sharp fixer fixes that apartment point. Hence the actual sharp
normalizer equals `sharpNormalizerStabilizer`. For parahoric data the same fixing
conclusion holds for normalizer elements in the full point parahoric.

For a chamber, membership in its full parahoric implies membership in the point
parahoric at every chamber point. Thus a normalizer element of this parahoric
acts trivially on the entire apartment. Under the additional explicit comparison
`P.zeroDatum.CoverImageCentralizerNormKernelStatement`, the actual chamber
normalizer intersection equals the actual centralizer-zero image. The entry
`chamberZeroNormalizerEquivCentralizerZeroImage` is the identity multiplicative
equivalence between those two subgroups.
Its application lemma records equality of the underlying rational point.

## Implemented proof

Point sharp exchange writes a normalizer element of the sharp fixer as
`v w m`, where the first two factors are opposite and original unipotent and
the last factor is a normalizer element fixing the point. The normalizer element
`n m⁻¹` therefore lies in the opposite-unipotent/unipotent product. The existing
affine opposite-cell separation makes this element trivial, so `n = m` fixes
the point.

The actual full-parahoric product formula writes an element as `z g`, with
`z` in the centralizer-zero image and `g` in the sharp fixer. If the product
normalizes the torus, then so does `g`. The preceding argument makes `g` fix
the point; omega compatibility makes `z` fix every apartment point.

The supporting affine-geometric lemma proves that a chamber of a locally finite
reflection arrangement spans its affine space. At its regular defining point,
the published local sign lemma permits a positive small displacement in each
vector direction without changing any root sign. Both endpoints lie in the
chamber, so the displaced vector belongs to the direction of its affine span.
Rescaling proves that direction is the whole vector space. This proof applies
also in rank zero and uses no choice of topology on the apartment.
Two affine maps agreeing on an affine-spanning set are equal, so fixing every
chamber point makes the actual normalizer affine equivalence the identity.

Finally the published apartment-root cover theorem puts the chamber parahoric
inside the actual zero subgroup. The conditional exact action-kernel theorem
for the zero-component normalizer then gives centralizer-zero membership.
The reverse inclusion follows from the centralizer-zero image lying in both the
normalizer and the actual parahoric. `MulEquiv.subgroupCongr` gives the entry.

## Provenance and retained obligations

All assertions are deductions from existing Library interfaces. This unit
introduces no external source assertion and requires no Dynamic ordered-product
premise. It does not prove opposite factor-pair existence or the cover
comparison. In particular it does not prove the unconditional
`ChamberParahoricNormalizerStatement` or the closing affine Iwahori–Tits
statement. Their original hypotheses remain unchanged.
