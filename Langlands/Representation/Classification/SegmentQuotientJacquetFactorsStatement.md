# Ordered Jacquet factors of a weak segment quotient

Authors: Worker 485 (statement design) and Worker 949 (submission edits).

`Langlands.Classification.SegmentQuotientJacquetFactors.{uF,uV} F T` is a
proposition definition. It states an object-level factorization of the actual
normalized upper Jacquet module for every ordered standard block shape of every
weak segment quotient. **This file proves no factorization or vanishing.**

## Statement

Fix a prime `p`, a p-adic field `F : PadicField.{uF} p` and supplied topological
data `T`. The universes `uF,uV` are independent. Under `letI := T.topology`,
let `Δ : T.Segment.{max uF uV,uF}` have length `m`, rank `r` and degree
`m * r`. Let `π` be an actual smooth complex representation of `GL_(m*r)(F)`
with carrier in `Type (max uF uV)`, satisfying only
`T.IsSegmentQuotient Δ π`. This is the weak irreducible-quotient relation for the
increasing induction; it supplies no strong-head uniqueness.

For every `B : GeneralLinear.BlockShape Δ.degree`, one of these alternatives
holds:

1. `B.JacquetModule π.representation` is a subsingleton. This is the actual
   coinvariant carrier of `T.normalizedJacquet B π.representation`, so this
   alternative says that the Jacquet representation is zero.
2. There exist positive integers `k i` indexed by the actual ordered set
   `Fin B.length`, segments `Γ i`, degree equalities `hdeg i`, and actual smooth
   block representations `σ i` with the following properties. Write
   `K i = ∑ j : Fin B.length with j < i, k j`. Then
   `B.size i = r * k i`, `∑ i, k i = m`, and `Γ i` has length `k i` and base
   `Δ.member (m - K i - k i)`. The equality
   `hdeg i : (Γ i).degree = B.size i` transports `σ i` from the actual group
   `GL_(B.size i)(F)` to the degree required by
   `T.IsSegmentQuotient (Γ i)`. That weak quotient relation holds for each
   transported factor. Finally there exists an actual complex-linear
   representation equivalence
   ```
   (T.normalizedJacquet B π.representation).Equiv
     (B.blockTensor (fun i => (σ i).representation)).
   ```

Write `ρ = Δ.base`, so that `Δ.member j = ν^j ρ`. Since a segment is
determined by its base and length, `Γ i` is the subsegment
`[ν^(m - K i - k i) ρ, ν^(m - K i - 1) ρ]` of `Δ = [ρ, ν^(m-1) ρ]`. Factor `0`
ends at `ν^(m-1) ρ`, and each later factor ends immediately below the
beginning of the previous one, so the factors are the successive intervals of
`Δ` in descending order. Natural subtraction is used in the base index. The positivity and total-sum conditions imply `K i + k i ≤ m`;
the subsegments do not extend outside `Δ`. The segment data are existential
to keep every tensor factor on the actual block group without introducing a
new segment construction.

The equivalence is of representations of the same actual block Levi
`B.Levi F.Carrier`. The tensor carrier is the existing `PiTensorProduct`;
`B.blockTensor` is the published external tensor action. The conclusion concerns
the entire Jacquet module, rather than a selected composition factor.

All shapes are included, in particular the one-block shape. There are no
nonzero, admissibility, finite-length, unitary, analytic or scalar-character
premises. Because `Δ` has positive length and rank, its degree is positive;
an empty positive-block shape cannot have this degree. For a block whose size
is not divisible by `r`, the second alternative is impossible and the first
asserts vanishing. The statement does not separately assert nonvanishing for
every shape with divisible block sizes.

## Normalization and provenance

This is an internal derived assertion, not a verbatim theorem of a cited
source. Its intended source route uses the registered
`zelevinsky-1980-induced-ii`, A. V. Zelevinsky, *Induced representations of
reductive p-adic groups II*, Ann. Sci. ENS (4) 13 (1980), 165–210,
SHA-256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
Section 9.1, printed p.197 / PDF p.34, characterizes the special constituent
as the unique irreducible quotient of the increasing segment induction and
gives its descending minimal Jacquet tensor. Section 9.5, printed p.198 /
PDF p.35, gives the proper two-block vanishing and tensor formula, with the
terminal subsegment first and the initial subsegment second. Its proof refers
to §3.4, printed pp.181–182 / PDF pp.18–19. The source uses `m` for the cuspidal
rank and `k` for the segment length, whereas this description uses `r,m`.

The Library's upper block parabolic uses increasing induction with positive
half-modulus covariance and right translation. Its normalized Jacquet action
has inverse half modulus. Iterating the proper two-block formula with
normalized transitivity in the actual order of the blocks yields descending
intervals in this normalization. No opposite-parabolic result is substituted.

An exact proof must independently supply the passage from every weak quotient
to the requisite special head, the proper two-block calculation and vanishing,
the one-block case, arbitrary-shape transitivity, external tensor Jacquet
compatibility, ordered tensor regrouping, and all representative and degree
transports. Pending statements, shared drafts and citations provide none of
those proofs. The scalar norm formula for all generalized eigencharacters is a
separate consumer and is not asserted here.

## Independence

Any proof of this statement and every prerequisite it uses must remain
independent of forward special essential square-integrability, parent ordered
conversion, square-integrable exhaustion, regular exhaustion, square-integrable
classification, analytic strong-head classification, tempered block uniqueness,
multisegment exhaustion, ordered strong-head existence, quotient coverage,
segment-head product irreducibility, generic segment-product uniqueness and
Zelevinsky multisegment socle exhaustion. These exclusions cover mathematical
conclusions, exact proof successors and transitive consequences. Derivative
formulas, Zelevinsky §9.3's analytic result and §9.17's conjecture cannot supply
this algebraic assertion.
