# Adjacent unlinked segment-socle swaps in a full induced product

Author: Worker 491. Worker 494 supplied the exact target and its dependency
independence requirements.

`Langlands.Classification.AdjacentUnlinkedSegmentSocleSwap.{uF,uV} F T` is a
Prop-valued definition stating the actual-product form of Zelevinsky 1980,
Proposition 6.4(1). This module states the assertion and supplies no proof.

## Exact scope and conventions

Fix any prime `p` with `Fact p.Prime`, any `F : PadicField.{uF} p`, and any
supplied compatible `T : F.TopologicalData`. The field and carrier universes
`uF` and `uV` are independent. Set `v = max uF uV`; segment bases, supplied
blocks and induced products here have carriers in `Type v`. The proposition
installs `T.topology`.

For every natural rank `n` and every actual
`d : T.SegmentProductDatum.{v,uF} n`, assume `d.HasSegmentSocles`. For every
`j : ℕ` and `h : j + 1 < d.length`, assume that the segments at positions
`⟨j, by omega⟩` and `⟨j + 1, h⟩` are not linked. The first index bound follows
from the same `h`. The conclusion is exactly

```text
Nonempty (d.induced ≅ (d.permute (d.shape.adjacentSwap j h)).induced)
```

This is a categorical isomorphism in the actual smooth complex representation
category of `GL_n(F)`, hence invertible equivariant complex-linear maps. The
normalized product uses the standard upper block parabolic, positive
half-modulus covariance, and right translation, with
`ν = |det|_F` and residue normalization `|varpi|_F = q^(-1)`.

`HasSegmentSocles` requires each supplied block to be the irreducible socle
of its segment's increasing cuspidal product, Zelevinsky's `⟨Δ⟩` from §3.1.
It does not assert existence of a chosen representative or use the special
head of that product. With `σ = d.shape.adjacentSwap j h`, the existing
`d.permute σ` puts the old segment and its actual block with label `σ i` at
new position `i`. This direction is from a new position to its old label.
The dependent block ranks agree by the definition of the permuted datum.
All occurrences and supplied representatives are retained, including repeated
and equal segments.

Only the indicated adjacent pair must be unlinked. There is no precedence
order, global pairwise nonlinkage, whole-product irreducibility, finite-length
premise, or supplied two-factor commutation premise. Every natural rank is
quantified. At rank zero, positivity of segment degrees and their degree sum
exclude the adjacent pair required by `h`, so this case is vacuous.

## Original source and precise translation

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
165–210, is registered as `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The retained original is
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.

Proposition 6.4(1), printed p.189/PDF p.26, asserts equivalence of the
products of segment socles when their ordered segment sequences differ by
transposing two unlinked neighbours. Its condition (1) does not require the
precedence condition in (2), or the existence theorem 6.1(a). The present
interface expresses equivalence as an actual categorical isomorphism and
retains the particular representatives already supplied in `d`. Transport
between representatives and through induction is functorial; no canonical
representative or semisimplification replaces those blocks.

The printed proof invokes associativity and commutativity in §§1.7 and 1.9
and the irreducibility criterion in Theorem 4.2. Theorem 1.9, printed
p.174/PDF p.11, asserts equality of composition-factor multisets for
finite-length products. By itself it gives no isomorphism of arbitrary
products. Theorem 4.2, printed p.184/PDF p.21, makes the two-factor products
of unlinked segment socles irreducible. Combining that independently proved
criterion with independently proved constituent comparison yields an actual
two-factor isomorphism. Induction in stages and functorial transport then
insert that isomorphism into the full product, which may be reducible.
Associativity and the coordinate form of induction in stages are in
§§1.1(c), 1.5 and 1.7, printed pp.170–173/PDF pp.7–10.

For this contribution, the original was read at printed pp.170–171,
173–174, 183–185 and 188–190/PDF pp.7–8, 10–11, 20–22 and 25–27;
Proposition 6.4 was also checked in the rendered p.189. No source-specific
errata directory or matching errata note was present in the supplied public
notes. The published guidance on segment-head independence was read and
its distinction between heads and socles is preserved.

## Dependency boundary and intended proof

The sole direct import is the unchanged
`Classification.SegmentProductPermutation`, which supplies the actual datum
permutation and imports the adjacent merge shapes. This statement neither
imports nor applies `AdjacentUnlinkedSegmentSwap`, the distinct special-head
commutation target.

The independent two-factor socle isomorphism must be proved before it is
lifted here. In particular, the two-block specialization of this full-product
conclusion cannot serve as its own input. The existing
`Classification.SegmentSocleProductIrreducibility` is the intended
irreducibility input; its proposition definition is not a proof.
Composition-factor commutativity, the requisite finite-length results, and
passage from irreducible constituent equality to an actual isomorphism also
remain proof obligations unless independently published.

For the lifting step, the existing adjacent merge and swapped refinement
constructions give the same outer shape and their exact consecutive-coordinate
identities. Apply independently proved `Parabolic.OrderedProductRegrouping`
on each side. At the merged slot use the independent two-factor socle
isomorphism, with the specified rank transports. At every other slot use
the identity, identifying singleton inner products by the actual single-block
induction equivalence. Map this family of isomorphisms through the outer
normalized product functor and reverse the swapped-side regrouping.
The existing coordinate-normalization and refined induction/tensor proof
owners are reusable lower inputs, not assumed completed results.

The eventual proof must be independent, directly and transitively, of
`OrderedMultisegmentSocleExistence`, independent socle exhaustion,
segment analytic classification, special-head multisegment exhaustion,
ordered special-head existence, quotient coverage, tempered block uniqueness,
`SquareIntegrableLanglandsClassification`, square-integrable exhaustion,
and regular exhaustion. Shared lower results may be used only after their
proof dependencies are checked. The proof Markdown must record that audit.
A proposition definition, citation, conditional assembly or pending task is
not a proved mathematical input.
