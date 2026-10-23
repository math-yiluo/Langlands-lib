# Existence of symmetric ample line bundles over a field

`Langlands.GroupScheme.FieldSymmetricAmpleExistenceStatement` is a
`Prop`-valued definition. It states an existence theorem; this module supplies
no proof of that theorem.

For every field `K : Type u` and every actual group scheme
`G : Grp (Over (Spec (CommRingCat.of K)))`, assume
`IsCommMonObj G.X`. If the structure morphism `G.X.hom` is smooth, proper,
and geometrically connected, then there exists
`L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left` such that
`L.IsAmple` and

\[
[-1]^*L \cong L.
\]

The isomorphism assertion is `Nonempty` of the categorical isomorphism type
between the actual module sheaves. The existential line bundle and its two
properties are conclusions, not supplied data or additional hypotheses.

## Published constructions and exact ampleness condition

`LineBundle X` is the published full subcategory of actual `X.Modules`
whose objects are locally isomorphic to the structure sheaf. Thus `L.obj`
is a locally free rank-one module sheaf. The published
`Langlands.GroupScheme.multiplication G m` is the integer power of the
identity in the pointwise group of homomorphisms. Its action on sections is
integer powering, the multiplicative notation for multiplication by `m`.
At `m = -1` this is inversion. Symmetry uses precisely
`AlgebraicGeometry.Scheme.Modules.pullback` along the actual scheme map
`(multiplication G (-1)).hom.hom.left`. No abstract action or symmetry
certificate is introduced.

For `X = G.X.left`, the imported predicate `L.IsAmple` means

```text
CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
  x ∈ L.sectionOpen s ∧ IsAffineOpen (L.sectionOpen s).
```

Here `L.powSections n` consists of global sections of the actual sheafified
tensor power `Langlands.Scheme.Modules.tensorPow L.obj n`.
`L.sectionOpen s` is the largest open on which the section-induced morphism
from the structure sheaf to that power is an isomorphism. The whole
generation open must be affine. Compactness is quasi-compactness of the
underlying scheme. The positive exponent bound is part of ampleness.

## Original sources and derived provenance

The main source is J. S. Milne, *Abelian Varieties*, the 1986
*Arithmetic Geometry* article, author corrected version dated January 2, 2022,
registered as `milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The retained file is
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`;
its original is the [author's PDF](https://www.jmilne.org/math/xnotes/AVs.pdf).
Printed and one-based PDF page numbers agree.

Corollary 7.2, p.12, states existence of a symmetric ample invertible sheaf
on every abelian variety. Its proof first invokes Theorem 7.1, pp.10–12,
to obtain an ample invertible sheaf `M`. Inversion is an isomorphism, so
`[-1]^*M` is ample, and `M ⊗ [-1]^*M` is ample and symmetric. Theorem 7.1
first proves projectivity over an algebraically closed field and then
descends an ample divisor, including the finite purely inseparable case.
Thus algebraic closure or perfectness is not a hypothesis of the conclusion.

Section 20, opening definition on p.42, presents abelian schemes as smooth
proper group schemes with connected geometric fibres and identifies their
fibres as abelian varieties. Specializing to `Spec K` gives this target.
Milne's conventions on p.2 require varieties to be separated, finite type,
and geometrically integral. Properness supplies separatedness and finite
type. After passage to an algebraic closure, smoothness supplies regularity;
a connected regular noetherian scheme has disjoint open irreducible
components and hence is integral. The identity section supplies nonemptiness.
These facts explain the comparison of presentations; this module does not
formalize that comparison. Explicit commutativity matches abelian varieties
and is required by the published bundled multiplication construction.

The imported ampleness predicate follows Stacks Project Definition 28.27.1,
tag [01PS](https://stacks.math.columbia.edu/tag/01PS), using the generation-open
presentation of the locus in Lemma 17.25.10,
tag [01CY](https://stacks.math.columbia.edu/tag/01CY). Both were read in the
registered source `stacks-invertible-picard-ampleness-2026-10-21`, retained
folder `literature/Stacks Project - Invertible sheaves, Picard groups and ampleness (HTML snapshot 2026-10-21)`,
files `01PS.html` and `01CY.html`, folder SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`.
Tag 01PS requires quasi-compactness and an affine nonvanishing locus of a
positive tensor-power section through each point. Tag 01CY identifies the
nonvanishing locus of a section of an invertible sheaf with the locus on
which that section is a frame, giving the mathematical correspondence with
the Library generation open.

Milne's Remark 7.3, p.12, uses the convention that some positive power of an
ample sheaf is very ample. On the proper finite-type schemes here this agrees
with the affine-locus definition: a very ample power has generating sections
whose nonvanishing opens are inverse images of standard affine projective
charts, and a closed projective embedding makes those opens affine. Conversely,
the ample affine-locus criterion on a proper scheme over a field yields a very
ample positive power. The latter comparison is not proved by this module and
is not required as an additional hypothesis. For transferring the existence
conclusion from Milne, the forward direction suffices.

Even the comparison between the Library generation opens and the Stacks
nonvanishing opens is not silently treated as an unconditional Lean result.
The published `LineBundle.isAmple_iff_nonvanishingLocus` requires
`LineBundleResidueOpenComparison` and local rank one of every actual tensor
power. Its conditional interface does not discharge those premises.
Any future proof using this comparison must prove or import them.

The provenance is therefore derived: Corollary 7.2 is expressed in
Section 20's field group-scheme presentation and with the published concrete
module-sheaf and generation-locus definitions. The preceding source and
definition comparisons explain that translation, not a completed Lean proof.

## Scope and proof boundary

The field is arbitrary, in every characteristic. No algebraic closure,
perfectness, positive dimension, projectivity, ample bundle, or polarization
is assumed. Dimension zero is included. This is a field statement, with no
claim of global ample existence over an arbitrary base.

A separate exact-target proof must establish this proposition after its
publication. Following Milne requires projectivity or ample existence,
preservation of ampleness under isomorphism pullback and tensor product,
local rank one for the constructed tensor sheaves, the inverse involution,
and the relevant tensor and pullback coherence isomorphisms. Existing
published lemmas may discharge parts of these obligations, but none is
installed as a constructor field or a hypothesis of this target. The source
comparison obligations above likewise remain proof work. This module adds
no axiom and proves none of the substantial geometry.
