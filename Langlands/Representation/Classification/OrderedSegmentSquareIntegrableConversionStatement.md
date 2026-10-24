# Ordered segment products and square-integrable Langlands data

Author: Worker 78.

`Langlands.Classification.OrderedSegmentSquareIntegrableConversion.{uF,uV} F T`
is a proposition definition. It states an internal derived conversion interface;
it neither proves the conversion nor assumes it as an axiom. Its only direct
import is the published `Langlands.Representation.Classification.LanglandsData`.

## Quantifiers and the common output datum

Fix an arbitrary prime `p`, `F : PadicField.{uF} p`, and the supplied realization
`T : F.TopologicalData`. The field universe `uF` and carrier parameter `uV` are
independent. Put `v = max uF uV`. For every natural number `n > 0` and every
`d : T.SegmentProductDatum.{v,uF} n`, the only hypotheses are:

- `d.IsPrecedenceOrdered`: for indices `i < j`, the segment `d.segments i`
  does not precede `d.segments j`;
- `d.HasSegmentHeads`: each actual block `d.blocks i` is the irreducible head
  of its own increasing segment induction, including uniqueness of the
  irreducible quotient kernel.

The conclusion chooses one `e : T.SquareIntegrableLanglandsDatum.{v,uF} n`
for which both of the following hold:

1. `Nonempty (d.induced ≅ e.induced)`, an actual isomorphism in the category
   of smooth complex representations of `GL_n(F)`.
2. There is a bijection `σ : Fin d.length ≃ Fin e.shape.length` such that
   for every original index `i` there is an equality
   `h : (d.segments i).degree = e.shape.size (σ i)` and an actual block
   isomorphism `Nonempty ((h ▸ d.blocks i) ≅ e.blocks (σ i))`.

The equality transport changes the group rank index of the original block.
The bijection preserves all blocks with multiplicity; it allows neither
merging nor discarding blocks. Both clauses concern the same existential `e`.
The statement does not prescribe a canonical permutation or chosen isomorphism.

The published output structure carries positive block ranks summing to `n`,
actual irreducible blocks, the analytic predicate
`T.IsEssentiallySquareIntegrable` for each block, and genuine
`UnitaryExponentData`. The latter consists of a real exponent `α` and an
invariant positive definite Hermitian form on `ν^(-α)` times the block.
Its `antitone` field imposes weakly decreasing exponents. Equal exponents
are permitted. No additional admissibility or unitarity hypothesis is imposed
on `d`; establishing the analytic output fields belongs to the future proof.

Segments, their supercuspidal representatives, both families of blocks, and
both induced carriers all use the saturated universe `v`. In particular,
`max uF v = v`, so the existing constituent relations and the two categorical
isomorphism types compare objects in the same carrier universe without
identifying `uF` and `uV`.

## Normalization and why reordering is substantive

The imported induction is normalized induction from the standard upper block
parabolic, acting by right translation with covariance by the positive half
modulus. Here `ν = |det|_F` uses the residue-normalized absolute value.
For `Δ = [ρ, νρ, …, ν^(m-1)ρ]`, the block hypothesis selects the special
quotient of the increasing product, called `St_m(ρ)` by Henniart. It is not
the segment socle of that increasing product.

Nonprecedence is a condition on linked segments and their positive integral
twists. It does not by itself assert that the real unitary exponents are
decreasing: unrelated unlinked segments may occur in either exponent order.
The intended derivation first identifies the actual segment heads as
essentially square-integrable and equips them with unitary exponent data.
For a segment of length `m`, its head has exponent
`α(ρ) + (m - 1)/2`. This formula and existence of `α(ρ)` are mathematical
inputs to be proved, not definitions or hypotheses in this module.

For linked segments, their starting and ending twists determine the same
strict order on their mean exponents. Thus an adjacent strict inversion of
the head exponents in a nonprecedence ordering must involve unlinked segments.
Commuting their special-head factors gives an actual isomorphism of the
adjacent induced products. Swapping an unlinked adjacent pair preserves
nonprecedence. Finite sorting by these swaps then yields decreasing exponents,
a rank-preserving permutation, and an isomorphism of the whole products.
Equal exponents need not be swapped or grouped. This explains the proposed
route; none of these analytic or reordering facts is proved in this file.

## Provenance and source boundaries

This exact interface, including the common actual datum, full-product
isomorphism and dependent block matching, is an internal derived assertion.
It is motivated by the following registered originals, whose cited passages
and complete local arguments were read:

- F. Rodier, *Representations de GL(n,k) ou k est un corps p-adique*,
  Seminaire Bourbaki, expose 587, Asterisque 92–93 (1982), pp.201–218.
  Source `rodier-1982-gln`, SHA256
  `389a9155f59022f5f5403bf568216f66b407b6d47e98221d115dcd85e076c8fc`.
  Section 4.3, Theorem 3 and the following argument, pp.211–212
  (PDF pp.12–13), present the ordered segment-head classification and its
  reduction using square-integrable and tempered blocks and the nonlinkage
  irreducibility criterion. Proposition 9(ii), p.210, records essential
  square-integrability of the special quotient. These passages motivate the
  conversion but do not state this exact product-isomorphism assertion.
- G. Henniart, *Une caracterisation de la correspondance de Langlands locale
  pour GL(n)*, Bull. Soc. Math. France 130 (2002), pp.587–602.
  Source `henniart-2002-characterization`, SHA256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
  Sections 2.5–2.8, pp.594–596 (PDF pp.8–10), fix upper normalized induction,
  identify special segment quotients with essentially square-integrable
  classes, and describe the unitary exponent normalization and weakly
  decreasing square-integrable Langlands data. The class-level assertions
  motivate the actual representation witnesses required here.

Rodier's closing sentence in section 4.3 says Theorem 2 where the local context
indicates Theorem 3; this is a contextual correction, not a new theorem.
The public classification source notes also retain the boundary that Rodier's
citation of Jacquet for tempered exhaustion does not provide a proof of
exhaustion in that cited article. Henniart's displayed dual formula in
section 2.6 omits the dual on the cuspidal factor, as already recorded in the
public coverage note. This module uses no contragredient formula and does not
use tempered exhaustion. The source-specific `notes/errata` files were absent
from the supplied Library and shared notes; the published classification
coverage and source-boundary notes were read for their retained corrections.

## Future proof obligations and scope

A proof must supply the analytic identification of segment heads, genuine
unitary normalization and its exponent formula, the linkage/exponent
comparison (including nonperiodicity of real norm twists), actual commutation
of unlinked special blocks, and finite sorting with rank and block transport.
To compose adjacent swaps inside a larger product it must also supply actual
normalized-induction transitivity and the relevant tensor and block-shape
identifications. Equality of composition factors or of a quotient class alone
would not supply the required isomorphism of full induced representations.

The published `SegmentSpecialEssentialSquareIntegrability` and the exponent
criterion in `SquareIntegrableExponentStatement` name relevant analytic
statement targets; their publication does not supply their proofs. A unitary
scalar central character alone is not substituted for the invariant positive
form in `UnitaryExponentData`.

No head, quotient, classification or exhaustion theorem for the full product
is a hypothesis or conclusion here. Once this conversion is proved, a separate
argument that already has a head of `d.induced` can transport that relation
along the resulting isomorphism using `SmoothRep.equivOfIso` and
`Classification.IsIrreducibleHead.of_equiv`. This preserves the given output
representation and transports the unique quotient-kernel condition. It does
not construct a head, prove square-integrable Langlands exhaustion, group equal
exponents, or prove uniqueness of exponents under isomorphism.
