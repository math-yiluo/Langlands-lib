# Existence of ample line bundles over an algebraically closed field

`Langlands.GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement` is a
universe-polymorphic `Prop`-valued definition. This module states the
existence result and supplies no proof.

For every field `K : Type u` with `IsAlgClosed K`, every actual
`G : Grp (Over (Spec (CommRingCat.of K)))`, and every commutativity instance
`IsCommMonObj G.X`, it asserts

```text
Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
  ∃ M : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left, M.IsAmple.
```

This is the published `Langlands.GroupScheme.FieldAmpleExistenceStatement`
with exactly one added hypothesis, the instance `IsAlgClosed K`. The
universe, group object, commutativity instance, three geometric hypotheses
and conclusion are unchanged. The module does not import the
arbitrary-field statement and is not its proof. It is the
algebraically closed input to the arbitrary-field reduction coordinated by
Worker 404, whose remaining inputs are the separate finite-extension
descent and finite-stage spreading statements.

Worker 299 implemented this pair. The hypothesis pattern, conclusion and
source comparison adapt the published arbitrary-field statement by
Worker 420. Worker 404 supplied the focused specification.

## Actual line bundles and the ampleness predicate

The statement uses the published `LineBundle` and `LineBundle.IsAmple`
unchanged. A line bundle on `X` is an object of the full subcategory of
actual `X.Modules` locally isomorphic to the structure sheaf.

For `X = G.X.left`, `M.IsAmple` is the proposition

```text
CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : M.powSections n,
  x ∈ M.sectionOpen s ∧ IsAffineOpen (M.sectionOpen s).
```

Here `M.powSections n` consists of global sections of the actual sheafified
tensor power `Langlands.Scheme.Modules.tensorPow M.obj n`. Its zeroth power
is the structure sheaf and its successor is the right-associated tensor
product, so the first power is `M.obj ⊗ 𝒪_X`, related to `M.obj` by an
isomorphism rather than definitional equality.

`M.sectionOpen s` is the largest open on which the map from the structure
sheaf sending one to `s` is an isomorphism. The entire open subscheme
defined by this generation locus must be affine; an affine neighbourhood of
`x` contained in it does not suffice. `CompactSpace X` is quasi-compactness
of the underlying space. The lower bound `1 ≤ n` is part of ampleness.
The sheaf and its ampleness are conclusions, not constructor fields,
certificates or premises.

## Original source

The original is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic
Geometry* article, author corrected version January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`,
retained as
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`;
the [author's PDF](https://www.jmilne.org/math/xnotes/AVs.pdf) is the
original. Printed and one-based PDF page numbers agree. Pages 2–3, 10–12
and 42 were read directly.

Theorem 7.1, pp.10–12, states that every abelian variety is projective.
Its proof begins: "We first prove this under the assumption that the
abelian variety `A` is defined over an algebraically closed field." In that
case it chooses finitely many prime divisors `Z_i` through `0` whose
intersection is `{0}` and which separate tangent vectors at `0`, and uses
the theorem of the square to show that `|3D|`, for `D = Σ Z_i`, is very
ample. The closing paragraph, which constructs an ample divisor over a
general ground field from one over a finite Galois or purely inseparable
extension, is not part of the present statement.

The proof of Corollary 7.2, p.12, starts: "According to the theorem, it has
an ample invertible sheaf `L`." The present statement isolates this first
step over an algebraically closed field. The subsequent symmetrization
`L ⊗ (-1)^* L` belongs to the downstream symmetric statement
`Langlands.GroupScheme.FieldSymmetricAmpleExistenceStatement`, which this
module neither imports nor needs.

Thus the statement is the algebraically closed portion of Theorem 7.1 and
the initial ample-existence step of Corollary 7.2, translated to actual
group schemes over `Spec K` and to the Library's ampleness predicate.

## Group-scheme presentation

The opening definition of Section 20, p.42, calls a group scheme over `S`
an abelian scheme when it is proper and smooth with connected geometric
fibres, and states that the fibres are then abelian varieties. For
`S = Spec K` this gives the three geometric hypotheses of the Lean
statement. They are kept in the parent's form, so `GeometricallyConnected`
is not replaced by connectedness even though `K` is algebraically closed.

Milne's conventions, pp.2–3, take a variety to be separated and of finite
type with integral base change to the algebraic closure, and an abelian
variety to be a complete connected group variety; such a variety is
automatically nonsingular. Over an algebraically closed `K` the base change
to the algebraic closure is isomorphic to the variety itself. Mathematically, the Lean
hypotheses give such a variety: properness supplies separatedness, finite
type and completeness; smoothness over the algebraically closed `K` gives
regularity, finite type gives noetherianity, and a connected noetherian
regular scheme is integral because its irreducible components are disjoint
and open. The unit section supplies a point. Corollary 2.4, p.3, shows that
the group law of an abelian variety is commutative; the instance
`IsCommMonObj G.X` is retained only to match the parent statement. This
paragraph explains the source correspondence; the module proves none of
these facts in Lean, and dimension zero is not excluded.

The complete [author errata](https://www.jmilne.org/math/articles/1986b.html)
were read in the registered retained original
`milne-abelian-varieties-1986-errata-2026-10-25`, SHA256
`e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`, file
`literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`.
The page states that all listed corrections are incorporated into the
xnotes version used here. Its imperfect-field correction concerns
Proposition 12.1; no listed entry concerns Theorem 7.1, Corollary 7.2,
Remark 7.3, the conventions or Section 20.

## Comparison with the generation-open definition

Milne's Remark 7.3, p.12, uses the convention that an ample invertible sheaf
has a very ample positive power. The registered original
`stacks-invertible-picard-ampleness-2026-10-21`, directory SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`,
retained in
`literature/Stacks Project - Invertible sheaves, Picard groups and ampleness (HTML snapshot 2026-10-21)`,
was read in `01PS.html` and `01CY.html`.
[Definition 28.27.1, tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
requires quasi-compactness and, through every point, an affine
nonvanishing locus `X_s` of a global section of some positive tensor power.
[Lemma 17.25.10, tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
shows that on `X_s` the map from the structure sheaf given by `s` is an
isomorphism, which matches the Library's whole generation open.

For existence only the passage from a projective embedding to this
condition is needed. Pull back the twisting sheaf along a closed embedding
into projective space. The pulled-back coordinate sections cover the
scheme, and each whole nonvanishing locus is a closed subscheme of a
standard affine chart, hence affine. Quasi-compactness follows from
properness over `K`. If a positive power is very ample, these sections are
sections of that power of the original sheaf.

This comparison is mathematical. It does not claim that Milne's
projectivity theorem, an actual projective embedding, or a comparison of
the pulled-back twisting sheaf and its coordinate sections with the
published tensor powers and generation opens is already formalized.
The published `LineBundle.isAmple_iff_nonvanishingLocus` assumes
`Langlands.SchemeModule.LineBundleResidueOpenComparison`, available as the
theorem `Langlands.SchemeModule.lineBundleResidueOpenComparison`, and local
rank one of every actual tensor power, the separate statement
`Langlands.AlgebraicGeometry.Picard.TensorPowLocallyFreeRankOneStatement`.

The provenance is derived: the algebraically closed case of Milne's
Theorem 7.1 and the ample-existence step of Corollary 7.2 are translated
through Section 20's group-scheme presentation into the published concrete
sheaf and ampleness definitions, with the hypotheses of the published
arbitrary-field statement plus `IsAlgClosed K`.

## Scope and subsequent proof

The statement covers every universe, every characteristic, and dimension
zero. Its only addition to the arbitrary-field statement is algebraic
closure. It adds no projectivity, geometric integrality, dimension,
polarization, existing ample sheaf, model, compatibility or certificate
premise; an eventual proof must derive such geometric inputs from the
given hypotheses.

After independent acceptance and publication, a separate exact-target
proof must have this entire named proposition as its type, with no extra
outer hypotheses. The concrete projective-space, actual projectivity and
twisting-sheaf prerequisites are coordinated with Worker 404. Existing
source-presentation, geometric-integrality, tensor-rank-one, residue,
pullback-comparison and ampleness-transport work is to be reused rather
than duplicated. This module adds no axiom and discharges none of those
proof obligations.
