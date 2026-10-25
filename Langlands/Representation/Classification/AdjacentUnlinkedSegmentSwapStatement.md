# Adjacent unlinked segment-head swaps in a full induced product

Author: Worker 328. Worker 17 supplied the exact target and its dependency
independence requirements.

`Langlands.Classification.AdjacentUnlinkedSegmentSwap.{uF,uV} F T` is a
Prop-valued definition. It states an actual isomorphism of normalized induced
representations; this module supplies no proof of that assertion.

## Exact scope

Fix any prime `p` with `Fact p.Prime`, any `F : PadicField.{uF} p`, and the
supplied `T : F.TopologicalData`. The field and carrier universe parameters
`uF` and `uV` are independent. Put `v = max uF uV`; the segment bases, supplied
blocks and induced representations use carriers in `Type v`. The definition
installs `T.topology`.

For every `n : ℕ` and `d : T.SegmentProductDatum.{v,uF} n`, assume
`d.HasSegmentHeads`. For every `j : ℕ` and `h : j + 1 < d.length`, assume only
that the two actual segments at positions `j` and `j+1` are not linked. With
`σ = d.shape.adjacentSwap j h`, the conclusion is

```text
Nonempty (d.induced ≅
  (T.normalizedProductInductionFunctor (d.shape.permute σ)).obj
    (fun i => d.blocks (σ i)))
```

The permutation sends a new position `i` to its original label `σ i`.
`BlockShape.permute` therefore gives the new block exactly the degree of
`d.blocks (σ i)`, definitionally. The conclusion retains every supplied
representation and every segment occurrence, including repetitions. By the
published `SegmentProductDatum.permute_induced`, the right side is also
`(d.permute σ).induced`. The isomorphism is in the actual smooth complex
representation category of `GL_n(F)`, hence consists of invertible equivariant
complex-linear maps.

Only the adjacent pair is required to be unlinked. Other pairs may be linked,
and the whole induced product may be reducible. There is no precedence order,
global pairwise nonlinkage, finite-length, whole-product irreducibility, or
supplied two-factor commutation premise. All natural ranks are quantified.
When `n = 0`, the degree sum and positivity of every segment degree exclude
such an adjacent pair. No rank-zero induction comparison is silently assumed.

## Conventions and derived provenance

The imported normalized induction uses the standard upper block parabolic,
positive half-modulus covariance and right translation. For
`Δ = [ρ, νρ, …, ν^(m-1)ρ]`, where `ν = |det|_F` and `|varpi|_F = q^(-1)`,
`HasSegmentHeads` selects the unique irreducible quotient of the increasing
cuspidal product, with the published quotient-kernel uniqueness condition.
It does not select the irreducible subrepresentation of that product.

This full-product statement is an internal derived interface, motivated by
the special-head product theory in the following registered originals:

- F. Rodier, *Representations de GL(n,k) ou k est un corps p-adique*,
  Seminaire Bourbaki, expose 587, Asterisque 92–93 (1982), pp.201–218.
  Source `rodier-1982-gln`, SHA256
  `389a9155f59022f5f5403bf568216f66b407b6d47e98221d115dcd85e076c8fc`.
  Proposition 9(ii), printed p.210 (PDF p.11), identifies the special
  quotient and its essential square-integrability. Section 4.1 on that
  page distinguishes `L(Δ)` from `Z(Δ)`. Section 4.3, printed pp.211–212
  (PDF pp.12–13), states the special-head classification and Proposition 13's
  nonlinkage irreducibility criterion, citing Zelevinsky Theorem 9.7.
- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
  pp.165–210. Source `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  Section 9.1, printed p.197 (PDF p.34), fixes the special quotient
  convention. Theorem 9.7(a),(b), printed p.199 (PDF p.36), and its argument
  in §§9.8–9.10, printed pp.199–201 (PDF pp.36–38), give the unlinked
  special-head product context; §9.10 identifies the unlinked product with
  an irreducible class determined by its multiset. In particular this
  motivates two-factor commutation independently of the larger product.

The cited passages were read in the retained originals, and both source
hashes were checked. PDF locators are one-based. No source-specific
`notes/errata` files were present in the supplied public notes. The published
`notes/henniart/gln-classification-sources.md` and the consumer
`OrderedSegmentSquareIntegrableConversionStatement.md` were read. Their
corrections and boundaries are retained: Rodier's closing reference to
Theorem 2 in §4.3 refers contextually to Theorem 3; the citation of Jacquet
there does not itself provide a proof of tempered exhaustion. Neither that
exhaustion nor Zelevinsky's omitted square-integrability converse is used as
an input here.

These source assertions do not state the exact full-product categorical
interface above. The two-factor input and its lifting through induction in
stages are separate mathematical obligations. Equality in a Grothendieck
group or matching Jordan–Hölder constituents alone does not establish this
target, since the full product need not be irreducible.

## Intended proof route and remaining inputs

The direct and swapped refinements in `Group.GL.AdjacentMergeShape` and
`Group.GL.AdjacentMerge` have the same merged outer shape. The intended
argument regroups each full product over that shape, applies an independently
proved two-factor isomorphism in the merged slot and identities on every
other supplied block, and reverses the regrouping on the swapped side.
The single-block identifications handle the remaining inner singleton
products. The constructions `normalizedProductInducedEquiv`,
`normalizedParabolicInducedEquiv`, `singleBlockNormalizedProductEquiv`, and
`normalizedRefinementInductionTransitivity` provide relevant actual
representation equivalences; the coordinate and tensor comparisons must
still be assembled with their precise rank transports.

The exact `Parabolic.OrderedProductRegrouping` proposition has a separate
proof owner. Its coordinate-normalization and refined induction/tensor
comparison inputs remain obligations until their proofs are published.
An independent proof of `Classification.TwoSegmentHeadCommutation` is the
intended two-factor input; publication of its planned statement would not
prove it. Independent irreducibility and constituent comparison, or a
suitable invertible intertwining operator, require their own proofs. This
module assumes none of those theorem targets as additional hypotheses.

The future proof must be independent, directly and transitively, of
`GenericSegmentProductUniqueness`, the parent ordered segment conversion,
square-integrable and regular exhaustion, square-integrable Langlands
classification, tempered block uniqueness, multisegment exhaustion,
ordered-head existence and quotient coverage. In particular, using the
two-block specialization of `GenericSegmentProductUniqueness` would create
a dependency cycle because its proof is intended to consume this adjacent
lifting result. Existing lower results may be reused after checking their
independence. A proposition definition, literature citation, draft or pending
task supplies no proved analytic or algebraic input.
