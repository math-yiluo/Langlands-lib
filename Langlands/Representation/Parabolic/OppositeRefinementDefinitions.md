# Actual opposite refinement geometry with a common Levi

This module constructs the opposite parabolic and its radical for a block
refinement, first inside the outer block Levi and then in the ambient general
linear group. It uses the existing subgroup `Geometric.refinedLevi R B S` for
both projections and both normalizer maps. All algebraic constructions work over
an arbitrary commutative ring `R : Type u`. The continuous versions require only
`TopologicalSpace R` and `IsTopologicalRing R`. There are no representation
carriers or representation universes in these interfaces.

## Sources and provenance

This is a derived type-A construction, with an internal extension from the
local-field setting of the sources to arbitrary commutative rings. The intrinsic
laws are proved in Lean from the published actual block geometry. The construction
reuses `GeneralLinear.BlockShape.oppositeLeviProjection`,
`oppositeLeviInParabolic` and `oppositeUnipotentSubgroup` from
`Langlands.Group.GL.OppositeBlocks`, and the common refined Levi and its product
identification from `Langlands.Representation.Geometric.RefinementDefinitions`.
The componentwise and subgroup-preimage proofs adapt the published upper
constructions in that module and in `Parabolic.RefinementPreimage` and
`Parabolic.RefinementComposition`; no upper subgroup or map is redefined.

The original sources motivating the geometry and the later consumer are:

- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472, §§1.7–1.8,
  pp.443–445 (PDF pages 4–6), and §§2.1–2.3, p.446 (PDF page 7).
  Source `bernstein-zelevinsky-1977-induced-i`, retained at
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`;
  SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  Section 1.7 introduces transport and the positive conjugation module;
  §1.8 specifies the normalizing Levi and radical setup and the normalized
  induction and quotient conventions. Sections 2.1–2.2 give parabolic triples
  and ordered block refinements for GL_n; §2.3 gives their functorial context.
- A. J. Silberger, *The Langlands quotient theorem for p-adic groups*,
  Math. Ann. 236 (1978), 95–104, §2, p.97 (PDF page 3), and Lemma 5.3,
  p.100 (PDF page 6).
  Source `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
  retained at `/home/taskhub/pilot/literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`;
  SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
  Section 2 defines the Jacquet quotient and discusses the opposite-parabolic
  quotient convention. Lemma 5.3 uses the opposite Jacquet modules at the outer
  and relative levels with a common smaller Levi. It motivates these interfaces;
  the lemma itself is not a result of this module.

These passages were read in the retained originals. No source-specific errata
files for these sources were present in the public notes at authoring time.
Neither source states these arbitrary-ring Lean definitions verbatim.

## Inner geometry

For a shape `B : BlockShape n` and `S : BlockRefinement B`, the subgroup
`Geometric.refinedOppositeParabolic R B S` is the product of the actual
`(S i).oppositeParabolic R` inside `B.Levi R`.
`refinedOppositeUnipotent R B S` is the product of the actual
`(S i).oppositeUnipotentSubgroup R`. The two `mem_...` lemmas express these
componentwise conditions.

`refinedOppositeLeviProjection` evaluates each component, takes its opposite
block projection, and applies the existing `refinedLeviEquiv` to obtain an element
of the same `refinedLevi R B S` used by the upper geometry.
`refinedOppositeLeviSection` includes the actual common block diagonal matrices
into the inner opposite parabolic; its underlying value is unchanged.
`refinedOppositeLeviProjection_section` proves that this is a section.

`refinedOppositeUnipotentRadical` denotes the projection kernel inside the
parabolic. `mem_refinedOppositeUnipotentRadical` identifies this kernel condition
with membership in the product radical. The proof reduces to each block's
published kernel definition, using the injective product-Levi equivalence.
`refinedOppositeUnipotent_le_parabolic` proves the ambient inclusion;
`refinedOppositeUnipotentRadical_map` identifies the ambient image of the kernel
with the product radical. `refinedOppositeLeviProjection_ker` also expresses it
as a subgroup preimage.

Normality of the kernel and its image proves
`refinedOppositeParabolic_le_normalizer`.
`refinedOppositeLeviNormalizer` restricts this normalization to the same refined
Levi; `refinedOppositeLeviNormalizer_val` identifies its value with `m.val`.
The `...Continuous` versions of projection, section and normalizer prove
continuity for the inherited product and subgroup topologies. Projection uses
the published component projections and the common Levi homeomorphism; the
other maps use continuous subtype inclusions.

## Full ambient geometry

The auxiliary `Parabolic.oppositeLeviPreimage R B H` is the image in GL_n(R)
of the subgroup preimage of `H ≤ B.Levi R` under the actual outer opposite
projection. Its membership lemma requires an actual outer opposite-parabolic
matrix whose diagonal projection is in `H`. The restricted projection and block
diagonal section are `oppositePreimageProjection` and `oppositePreimageSection`.
Their section law and continuous versions are proved. The lemma
`oppositePreimage_subgroup` proves compatibility of this construction with a
further subgroup preimage and ambient inclusion.

`composedOppositeParabolic R B S` uses this construction with the inner opposite
parabolic. `composedOppositeUnipotent R B S` uses it with the inner opposite
radical. Thus the latter includes the entire outer radical as well as the inner
radical embedded by `B.leviEmbedding R`; the explicit inclusion lemmas are
`oppositeUnipotentSubgroup_le_composedOppositeUnipotent` and
`refinedOppositeUnipotent_map_le_composedOppositeUnipotent`.
The first proof uses that an outer radical element projects to one, and the
second uses the block diagonal section.

`composedOppositeLeviProjection` composes the restricted outer projection with
the inner projection, again landing in `refinedLevi R B S`.
`composedOppositeLeviSection` composes the two sections and has underlying value
`B.leviEmbedding R m.val`. The section law proves surjectivity.
`composedOppositeLeviProjection_ker_map` identifies the ambient image of its
kernel with the full radical, by the subgroup-preimage lemma and the inner
kernel-image equality. `composedOppositeLeviProjection_ker` identifies the kernel
itself with the radical's preimage under the ambient inclusion.

These equalities prove the full radical lies in the composed parabolic and is
normalized by it. Restricting to the common Levi yields
`composedOppositeLeviNormalizer`; its `_val` lemma states exactly that its
underlying matrix is `B.leviEmbedding R m.val`. The projection, section and
normalizer each have a proved `...Continuous` version. These proofs compose
the already continuous maps and use the inherited subgroup topology.

## Normalization boundary for later consumers

For the later p-adic consumer, the explicit positive full characters are the
existing `T.refinedLeviModulus B S` and `T.composedLeviModulus B S`. The latter
multiplies the restricted outer full character by the inner full character.
The opposite convention will use their inverses as full characters on the same
refined Levi. Applying the Jacquet inverse-half normalization to an inverse
upper full character gives the positive half of the upper full character,
as used with the opposite quotient in Silberger's convention.
The quotient must be by the actual opposite radical defined here.

This module defines geometry only. It proves no Haar-modulus comparison,
Jacquet or induction functor transitivity, exactness, or classification theorem.
It introduces no normalized functors and does not identify the composed groups
with a flattened shape. Published flattening constructions are unchanged.
