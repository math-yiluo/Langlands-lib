# Flatness of finite surjective abelian endomorphisms over fields

`Langlands.GroupScheme.FieldFiniteSurjectiveEndomorphismFlatStatement` is a
`Prop`-valued definition. It states that for every field `K : Type u`, every
group object `G : Grp (Over (Spec (CommRingCat.of K)))` with `IsCommMonObj G.X`,
and every endomorphism `f : G ⟶ G`, the following implication holds:

- The structure morphism `G.X.hom` is smooth, proper, and geometrically connected.
- The underlying scheme morphism `f.hom.hom.left` is finite and surjective.
- Then that same scheme morphism `f.hom.hom.left` is flat.

Here finiteness, surjectivity, and flatness are Mathlib's `IsFinite`, `Surjective`,
and `Flat` on actual scheme morphisms. Surjectivity refers to the map on scheme
points; it does not assert surjectivity on `K`-rational points. Smoothness,
properness, and geometric connectedness concern the map to `Spec K`, not the
endomorphism. The universe `u`, the field, and its characteristic are arbitrary.
No proof of this proposition is supplied.

## Original source and correspondence

The source is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic Geometry*
article in the author's corrected version dated January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The retained copy is
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
Printed and one-based PDF pages agree. Pages 2–3, 6, 12, and 42 were read directly.
No errata note for this source was found in the available project notes.

Proposition 8.1 on p.12 equates, for a homomorphism `f : A → B` of abelian
varieties, condition (b), equal dimensions and surjectivity, with condition (d),
finiteness, flatness, and surjectivity. For an endomorphism `A = B`, the dimensions
are equal automatically. The present target extracts only flatness, with
finiteness additionally supplied as a hypothesis to isolate this geometric
obligation. It is a derived specialization, not a separately numbered theorem
in the source.

The group-scheme presentation follows the opening definition of §20 on p.42:
an abelian scheme has a smooth proper structure morphism and connected geometric
fibres. Over a field, the source identifies this condition with being an abelian
variety. Mathlib's `GeometricallyConnected` tests connectedness after field-valued
base change, which expresses the same geometric connectedness here. In the
source's conventions on p.2, varieties are geometrically integral separated
schemes of finite type. Smoothness, properness, and geometric connectedness give
this presentation over a field: after algebraic closure the scheme is regular
and noetherian, and connectedness makes its disjoint open irreducible components
a single component. The unit section ensures nonemptiness. This file does not
formalize that correspondence.

A morphism in `Grp (Over (Spec K))` is a morphism of `K`-schemes respecting the
group operations, as in the source's notion of homomorphism. Commutativity is
explicit in the Lean target; it holds for abelian varieties by Corollary 2.4,
p.3. The source works over an arbitrary fixed ground field (p.2). Its reduction
to an algebraically closed field in the proof of Proposition 8.1 is a proof step,
not a hypothesis of the proposition.

## Proof boundary

There is no algebraic-closure, perfectness, projectivity, kernel smoothness or
reducedness, flatness, locally free direct-image, or constant-rank certificate
hypothesis. In particular, this target includes inseparable finite surjective
endomorphisms in positive characteristic. It asserts neither étaleness nor a
degree formula.

Milne's proof on p.12 uses translations to compare fibres and then invokes
Theorem 4.2(d) to conclude local freeness of the finite direct image of the
structure sheaf from constant fibre dimensions. However, Theorem 4.2 as printed
on p.6 already assumes that its morphism is flat. Thus that invocation, taken
literally, cannot prove the present flatness conclusion without circularity.
This statement does not assume that step as a lemma.

A separate proof must establish a valid route, for example a suitable
finite-module constant-fibre-rank criterion over a reduced base, generic freeness
and translations, or miracle flatness with all its hypotheses established. These
are possible routes, not results provided by this file. In the pinned Mathlib,
the relevant finite-morphism rank identities and local constancy theorem in
`AlgebraicGeometry/Morphisms/FlatRank.lean` already assume flatness; they do not
supply this missing implication.

The existing `Langlands.AlgebraicGeometry.FiberwiseFlatnessStatement` assumes
flatness on every field fibre. Applying it over `Spec K` does not establish the
field-fibre input isolated here. The present module imports only Mathlib and
does not depend on `Langlands.GroupScheme.FieldFiniteKernelIsogenyStatement`.
The latter is an intended consumer, and using its conclusion to prove this
prerequisite would create a circular proof route.

After independent acceptance and publication of this statement, a separate
exact-target proof obligation must prove this unchanged proposition. Any
substantial missing definitions, statements, and proofs must be developed as
separate reviewed prerequisites. The eventual proof's Markdown must describe
the route actually implemented.

## Attribution

Worker 100 authored this statement pair from the focused specification and
source-route cautions supplied by Worker 139.
