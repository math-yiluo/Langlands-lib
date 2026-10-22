# Multiplication pullback of symmetric line bundles over a field

`Langlands.GroupScheme.FieldSymmetricMultiplicationPullbackStatement` is a
`Prop`-valued definition. It records a target for a later proof; this module
supplies no proof of that proposition.

For every field `K : Type u`, let
`G : Grp (Over (Spec (CommRingCat.of K)))` be an actual group scheme. Assume
`IsCommMonObj G.X` and assume its structure morphism `G.X.hom` is smooth,
proper, and geometrically connected. For every actual line bundle
`L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left`, assume symmetry:
there exists an isomorphism of module sheaves

\[
[-1]^*L \cong L.
\]

Then for every natural number `n` with `0 < n`, the target asserts the existence
of an isomorphism of module sheaves

\[
[n]^*L \cong L^{\otimes(n\cdot n)}.
\]

Both isomorphism assertions use `Nonempty` of the corresponding categorical
isomorphism type. Symmetry is a hypothesis on the given sheaf, and the
multiplication pullback isomorphism is the conclusion to be proved.

## Actual constructions and conventions

`LineBundle X` is the published full subcategory of `X.Modules` consisting of
sheaves locally isomorphic to the structure sheaf; `L.obj` is its underlying
module sheaf. It supplies the actual locally free rank-one sheaf corresponding
to an invertible sheaf in the source.

The published `multiplication G m` is the integer power of the identity in the
pointwise group of group-scheme homomorphisms. On sections it is the integer
power map, written additively as multiplication by `m`. Its underlying scheme
map is `(multiplication G m).hom.hom.left`. Thus `m = -1` is inversion and
`m = (n : ℤ)` is positive multiplication. Both pullbacks in the proposition
are the existing `AlgebraicGeometry.Scheme.Modules.pullback` applied to these
actual scheme maps. The imported line-bundle pullback module establishes
preservation of local rank one; the formula itself is stated in the ambient
module-sheaf category.

The right side uses the published `Langlands.Scheme.Modules.tensorPow`.
Its zeroth power is the structure sheaf; its successor is the sheafified
tensor product of `L.obj` with the previous power. Consequently these are
right-associated natural tensor powers with a final structure-sheaf factor.
The exponent `n * n` is computed in `ℕ`. This is the ordinary nonnegative
square, with no residue-characteristic reduction. No abstract Picard group,
additional power action, or monoidal-category structure is supplied as a
parameter. Comparing and combining these concrete tensor powers is work for
the later proof and its coherence prerequisites.

## Original source and precise specialization

The original source is J. S. Milne, *Abelian Varieties*, the 1986
*Arithmetic Geometry* article, author corrected version dated January 2, 2022.
It is registered as `milne-abelian-varieties-1986-author-2022`, content SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The retained file is
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`;
the [author's original PDF](https://www.jmilne.org/math/xnotes/AVs.pdf) is its
source. Printed and one-based PDF page numbers agree in this copy.

Corollary 6.6, p.9, first gives the general multiplication formula using the
powers `(n²+n)/2` and `(n²-n)/2` of an invertible sheaf and its inversion
pullback. It then explicitly gives the symmetric specialization
`[n]*L ≅ L^(n²)`. The target records precisely that symmetric conclusion for
positive natural `n`. The source writes symmetry with the isomorphism in the
opposite direction; reversing an isomorphism gives the condition used here.
Restricting the source's integer multiplication formula to `n > 0` permits
natural tensor powers only. The general formula, antisymmetric case, zero,
and negative integers are outside this target.

Section 20, opening definition on p.42, defines an abelian scheme as a smooth
proper group scheme with connected geometric fibres and identifies its fibres
as abelian varieties. Specializing the base to `Spec K` gives the group-scheme
presentation used here. The source's conventions on p.2 require a variety to
be separated, finite type, and geometrically integral. Properness supplies
separatedness and finite type. Smoothness gives regularity after algebraic
closure; a connected regular noetherian scheme is irreducible and reduced,
so geometric connectedness supplies the required geometric integrality. The
identity section guarantees nonemptiness. These observations explain the
source correspondence; this module does not formalize that comparison.
Commutativity is explicit because it is required by the published bundled
multiplication operation, consistently with the abelian varieties of the
source.

The field is arbitrary. Corollary 6.6 imposes no assumption on its characteristic
and no coprimality condition on `n`; in particular the statement includes
positive characteristic dividing `n`. Neither ampleness nor projectivity is
an additional hypothesis. Theorem 8.2, p.13, subsequently uses this identity
for a symmetric ample sheaf to prove finiteness of the multiplication kernel.
That application motivates this focused statement but asserts more than the
present module and remains separate work.

The provenance is the symmetric positive-natural specialization of
Corollary 6.6, expressed using Section 20's group-scheme presentation and the
published concrete sheaf constructions. Milne's proof on p.9 derives a
recurrence from the cube-theorem corollaries and uses induction. A separate
exact-target proof task must establish this Library proposition and split
substantial cube, square, or tensor/pullback coherence prerequisites before
implementing them. The statement assumes none of those intermediate results.
