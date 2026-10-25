# Existence of ample line bundles over an arbitrary field

`Langlands.GroupScheme.FieldAmpleExistenceStatement` is a universe-polymorphic
`Prop`-valued definition. This module states the existence result and supplies
no proof.

For every field `K : Type u`, every actual
`G : Grp (Over (Spec (CommRingCat.of K)))`, and every commutativity instance
`IsCommMonObj G.X`, it asserts

```text
Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
  ∃ M : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left, M.IsAmple.
```

The field, group object, instance, and three geometric hypotheses are exactly
those of the published `Langlands.GroupScheme.FieldSymmetricAmpleExistenceStatement`.
Only the inverse-pullback symmetry part of that statement's conclusion is
omitted. The present module does not import or use that existence statement.
It is intended as a prerequisite for its proof.

Worker 420 implemented this pair. The hypothesis pattern and source comparison
adapt the published symmetric statement by Workers 337 and 131. Worker 291
supplied the focused ample-existence specification and the source and
prerequisite boundaries used here.

## Actual line bundles and the ampleness predicate

The statement uses the published `LineBundle` and `LineBundle.IsAmple`
unchanged. A line bundle on `X` is an object of the full subcategory of
actual `X.Modules` locally isomorphic to the structure sheaf. In particular,
`M.obj` is an actual locally free module sheaf of rank one.

For `X = G.X.left`, `M.IsAmple` is the proposition

```text
CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : M.powSections n,
  x ∈ M.sectionOpen s ∧ IsAffineOpen (M.sectionOpen s).
```

Here `M.powSections n` consists of global sections of the actual sheafified
tensor power `Langlands.Scheme.Modules.tensorPow M.obj n`. Its zeroth power
is the structure sheaf, and its successor is the right-associated tensor
product. In particular, the first power is `M.obj ⊗ 𝒪_X`, and comparison
with `M.obj` uses an isomorphism rather than definitional equality.

`M.sectionOpen s` is the largest open on which the map from the structure
sheaf induced by `s` is an isomorphism. The entire open subscheme defined by
this generation locus must be affine. The condition does not merely ask
for an affine neighborhood of `x` lying inside that locus.
`CompactSpace X` is quasi-compactness of the underlying space of the scheme.
The lower bound `1 ≤ n` is part of ampleness.

The existential sheaf and its ampleness are conclusions. They are not
constructor fields, supplied certificates, or additional geometric premises.

## Original source and group-scheme presentation

The main original is J. S. Milne, *Abelian Varieties*, the 1986
*Arithmetic Geometry* article, author corrected version January 2, 2022,
registered as `milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The retained file is
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`;
the [author's PDF](https://www.jmilne.org/math/xnotes/AVs.pdf) is the original.
Printed and one-based PDF page numbers agree. Pages 1–3, 10–12 and 42 were
read directly.

Theorem 7.1, pp.10–12, establishes projectivity for every abelian variety.
Its proof first works over an algebraically closed field, then constructs
an ample divisor over the ground field from one over a finite extension.
The descent discussion includes finite Galois extensions and finite purely
inseparable extensions; in the latter case a suitable characteristic-power
multiple of the divisor descends. Thus algebraic closure and perfectness
are not hypotheses of the resulting existence theorem.

The first step of Corollary 7.2, p.12, obtains an ample invertible sheaf
from Theorem 7.1. This is precisely the existence conclusion isolated here.
The subsequent construction of a symmetric sheaf from that ample sheaf is
left to the symmetric existence theorem. No use of that theorem is needed
or permitted to prove the present prerequisite.

The opening definition in Section 20, p.42, presents an abelian scheme as
a smooth proper group scheme with connected geometric fibres and identifies
its fibres as abelian varieties. Specialization to `Spec K` gives the
geometric hypotheses in the Lean statement. Commutativity is explicitly
retained to match the published symmetric target.

Milne's conventions on p.2 require varieties to be separated, of finite
type, and geometrically integral. The conversion from the stated
group-scheme hypotheses uses actual geometric facts: properness supplies
separatedness and finite type; after extension to an algebraic closure,
smoothness gives regularity, and finite type gives noetherianity.
A noetherian regular scheme has disjoint open irreducible components,
so connectedness and nonemptiness make it integral. The unit section
supplies a point after every such field extension. These facts explain
the source presentation; this statement module does not prove the
presentation comparison in Lean.

The complete [author errata](https://www.jmilne.org/math/articles/1986b.html)
were checked on October 25, 2026, against the registered retained original
`milne-abelian-varieties-1986-errata-2026-10-25`, SHA256
`e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`,
file `literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`.
The page says the listed corrections are incorporated into the xnotes
version. Its imperfect-field correction concerns Proposition 12.1, not
Theorem 7.1 or Section 20; no listed correction changes the cited
projectivity or abelian-scheme statements.

## Comparison with the generation-open definition

The registered original `stacks-invertible-picard-ampleness-2026-10-21`
has directory SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`
and is retained in
`literature/Stacks Project - Invertible sheaves, Picard groups and ampleness (HTML snapshot 2026-10-21)`.
The originals `01PS.html`, Definition 28.27.1, and `01CY.html`, Lemma
17.25.10 and proof, were read directly.

Stacks [Definition 28.27.1, tag 01PS](https://stacks.math.columbia.edu/tag/01PS),
requires quasi-compactness and, through every point, an affine
nonvanishing locus of a global section of some positive tensor power.
[Lemma 17.25.10, tag 01CY](https://stacks.math.columbia.edu/tag/01CY),
identifies this locus for an invertible sheaf with the locus on which
the section is a frame, so that its induced structure-sheaf map is
an isomorphism. This gives the mathematical correspondence with the
Library's entire generation open.

Milne's Remark 7.3, p.12, uses the convention that an ample sheaf has a
very ample positive power. For existence, only the passage from a
projective embedding to the stated affine-locus condition is needed:
pull back the projective twisting sheaf along a closed embedding.
The pulled-back coordinate sections cover the scheme, and each whole
nonvanishing open is a closed subscheme of a standard affine projective
chart, hence is affine. If a positive power is used, its sections are
sections of that power of the original sheaf. Properness over the field
supplies the required quasi-compactness. This explains the direction
needed from Milne's convention; a converse comparison is not part of
this statement or a required premise.

Formalizing that route still requires constructing the actual module
sheaf and its local rank-one witnesses, matching the relevant sheaves
and sections to the published tensor powers, and identifying their whole
nonvanishing and generation opens. The published
`LineBundle.isAmple_iff_nonvanishingLocus` is conditional on
`Langlands.SchemeModule.LineBundleResidueOpenComparison` and local rank
one of every actual tensor power. It does not prove those premises.
Any future use must establish or import them, together with any needed
sheaf-isomorphism or scheme-isomorphism transport of ampleness.

The provenance is derived: the ample existence step of Milne's
Corollary 7.2 is translated through Section 20's field group-scheme
presentation and the published concrete sheaf and ampleness definitions.
The comparisons above describe mathematical correspondence and pending
formal obligations.

## Scope and subsequent proof

The statement includes arbitrary fields, every characteristic, imperfect
fields, and dimension zero. It adds no projectivity, existing ample sheaf,
perfectness, algebraic closure, polarization, or dimension premise.
It asserts existence over a field only.

After independent acceptance and publication, a separate exact-target
proof must have this entire named proposition as its type, with no extra
outer hypotheses. Its executor must inspect existing Library declarations
and task owners, then split substantial missing presentation,
projectivity and arbitrary-field descent, and concrete ampleness
comparison prerequisites into focused definition, statement, and proof
tasks in dependency order before implementing them.

Existing tensor rank-one, residue-locus, pullback comparison, and ampleness
transport work must be reused and coordinated with its owners. The
symmetric ample existence statement is a downstream consumer and cannot
be invoked to prove this prerequisite. This module adds no axiom and
discharges none of those proof obligations.
