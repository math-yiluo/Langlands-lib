# The balanced cube pullback identity over a field

`Langlands.GroupScheme.FieldCubePullbackStatement` is a `Prop`-valued
definition recording a target for a later proof. This module does not prove
the cube identity.

For a field `K : Type u`, take an actual group object
`G : Grp (Over (Spec (CommRingCat.of K)))`, with `IsCommMonObj G.X`.
Assume exactly that its structure morphism `G.X.hom` is smooth, proper,
and geometrically connected. Let `T` be any scheme over `K`, represented
by an object of the same `Over` category, and let `f g h : T ⟶ G.X` be
any three morphisms over `K`. For every
`L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left`, put

\[
Q(a)=a^*L.
\]

The proposition asserts existence of an isomorphism of module sheaves on
`T.left`:

\[
Q(f+g+h)\otimes\bigl(Q(f)\otimes(Q(g)\otimes Q(h))\bigr)
\;\cong\;
Q(f+g)\otimes\bigl(Q(f+h)\otimes Q(g+h)\bigr).
\]

## Exact constructions and scope

Lean writes the group operation multiplicatively: `f * g` is addition of
maps to the abelian variety. Opening `CategoryTheory.MonObj` activates
Mathlib's existing pointwise group structure on `T ⟶ G.X`. Its product is
the pairing of the two maps followed by the actual multiplication of `G`;
it is not composition of `f` and `g`. The expression `f * g * h` is
`(f * g) * h`. No operation on maps is supplied as an extra parameter,
and the maps need not be homomorphisms of group schemes.

`LineBundle` is the published full subcategory of locally free rank-one
module sheaves. The formula uses its underlying module sheaf `L.obj`.
The local abbreviation `Q a` is exactly
`(AlgebraicGeometry.Scheme.Modules.pullback a.left).obj L.obj`, where
`a.left` is the underlying scheme morphism. Each tensor is exactly
`Langlands.Scheme.Modules.tensorObj`, the sectionwise tensor followed by
module sheafification, published in
`Langlands.AlgebraicGeometry.Modules.Tensor`.

`Nonempty` wraps the categorical isomorphism type in `T.left.Modules`.
The displayed parentheses are the exact right-associated parentheses in
Lean. The statement therefore needs no assumed monoidal structure or
coherence theorem, and introduces no Picard group or tensor-power action.
The later proof must justify the necessary tensor rearrangements and
pullback comparisons using actual constructions.

The field is arbitrary, including positive characteristic. There is no
restriction of smoothness, properness, finite type, reducedness, or
connectedness on `T`. There is no ampleness, projectivity, algebraic
closure, or rigidification hypothesis on `G` or `L`. In particular, no
chosen trivialization of the fibre of `L` at the identity is part of the
data. The proposition asserts existence only.

## Source and derivation

The source is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic
Geometry* article, author corrected version dated January 2, 2022,
registered as `milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The retained copy is
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`;
the [author's PDF](https://www.jmilne.org/math/xnotes/AVs.pdf) is its origin.
Printed and one-based PDF page numbers agree.

Corollary 6.4, p.9, trivializes on `A × A × A` the tensor with positive
factors indexed by `123, 1, 2, 3` and inverse factors indexed by
`12, 23, 13`. Tensoring with the three pair factors gives the balanced
formula. This mathematical derivation uses invertibility of line bundles;
it does not add invertibility or cube identities as hypotheses in Lean.

The rendered original p.9 was checked: Corollary 6.5 prints `(f+h)^*L`
without an inverse, whereas Corollary 6.4 has `p₁₃^*(L⁻¹)`. The formula
here follows Corollary 6.4. Corollary 6.5's proof supplies the pullback
argument along `(f,g,h)`. Pulling back the isomorphism on `A³` works for
any scheme `T` over `K`, beyond the variety convention of p.2: functorial
pullback preserves isomorphisms, and its tensor comparison identifies the
factors. No geometric condition on `T` is used.

Section 20, p.42, identifies the smooth proper group-scheme presentation
with connected geometric fibres as an abelian scheme; over a field this
gives an abelian variety. Together with p.2's conventions, this explains
the formal geometric hypotheses. These comparisons describe provenance,
not additional results proved in this module.

## Separate proof obligation

The formal deliverable is the proposition alone. A separate exact-target
proof must establish this Library declaration without adding any cube,
descent, invertibility, or coherence assumptions to it. Its prerequisites
include the geometric cube statement and proof, actual tensor coherence,
canonical pullback-tensor invertibility, and the comparison between local
rank one and tensor invertibility. The symmetric multiplication formula
and its recurrence and induction are separate downstream results.
