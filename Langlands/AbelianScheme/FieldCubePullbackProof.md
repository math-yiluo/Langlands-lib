# The balanced cube pullback identity over arbitrary fields

Author: Worker 815.

The theorem `Langlands.GroupScheme.fieldCubePullback` proves the exact
Library proposition `Langlands.GroupScheme.FieldCubePullbackStatement.{u}`.
For an arbitrary field `K : Type u`, a commutative group object over
`Spec K` with smooth, proper and geometrically connected structure
morphism, an arbitrary scheme `T` over `K`, three arbitrary maps
`f,g,h : T → G`, and an actual line bundle `L` on `G`, set
`Q(a) = a^*L`. The conclusion is existence of an actual module-sheaf
isomorphism on `T`:

\[
Q(f+g+h)\otimes\bigl(Q(f)\otimes(Q(g)\otimes Q(h))\bigr)
\;\cong\;
Q(f+g)\otimes\bigl(Q(f+h)\otimes Q(g+h)\bigr).
\]

Lean uses the pointwise group operation on maps, written `*`, for these
sums. Its `Q(a)` is precisely the scheme-module pullback of `L.obj`;
every tensor is the published `Langlands.Scheme.Modules.tensorObj`.
The displayed parentheses agree with the statement. The universe `u`
is arbitrary.

## Implemented proof

The proof applies the published conditional assembly
`fieldCubePullbackOfIsomorphism` to the unconditional theorem
`Langlands.AlgebraicGeometry.Picard.fieldCubeIsomorphism.{u}`.
This discharges the assembly's only explicit premise.

The imported assembly constructs the positive four-factor tensor and
the negative three-factor tensor as actual line bundles on the
right-associated triple product of `G`. It obtains a trivialization of
the fibre of `L` at the identity from `fieldLineBundleTriviality`.
The three `BalancedCube` identity-fibre face comparisons then supply
isomorphisms between the restrictions of these two bundles on all
three faces. The two-bundle geometric cube theorem produces their
actual global comparison. Finally `pullCubeIso` pulls that comparison
back along the triple of maps `f,g,h`. The published
`pullbackTensorComparisonIsIso` identifies the resulting factors with
the exact sheaf tensors in the target.

The two-bundle comparison theorem in turn applies the geometric cube
triviality theorem to the tensor of one bundle with an existential
inverse of the other. Its local-rank-one, tensor-inverse and pullback
comparisons are discharged by published proofs. All these results are
imported by Lean name; this module adds only the final application.

The final theorem has the Library proposition itself as its type.
Its hypotheses contain no extra cube theorem, chosen fibre
trivialization, tensor inverse or coherence data. Its quantified domain
`T` is arbitrary, and the pullback step uses no geometric hypothesis on
`T`. No ampleness, projectivity, algebraic closure or characteristic
restriction is added.

## Source and provenance

This is the final internal composition of the published balanced tensor,
face, identity-fibre and pullback constructions with the published
two-bundle geometric cube proof. Their authorship remains recorded in
the imported pairs. No new geometric or tensor-algebra argument is
introduced here.

The underlying source is J. S. Milne, *Abelian Varieties*, author corrected
version of January 2, 2022 of the 1986 chapter. Corollary 6.4 on printed
and one-based PDF p.9 gives the alternating tensor with the three
inverse pair factors; balancing it gives the displayed formula.
Corollary 6.5's proof pulls back along the triple of maps. The rendered
p.9 omits the inverse on `(f+h)^*L` in the printed Corollary 6.5, so the
formal formula follows Corollary 6.4. The source conventions on p.2
and abelian-scheme definition in Section 20, p.42 explain the field
presentation. These passages and the complete retained author errata
were read; the errata do not address this omitted inverse.

Registered source `milne-abelian-varieties-1986-author-2022`, retained at
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`,
SHA256 `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Registered errata `milne-abelian-varieties-1986-errata-2026-10-25`,
retained at
`literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`,
SHA256 `e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`.
