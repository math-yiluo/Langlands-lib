# Inner automorphisms of group schemes

This is an internal construction from the group-valued Yoneda API in
`Multiplicative`. It applies to an arbitrary base scheme `S` and group scheme
`G` over `S`, without affineness or commutativity assumptions.

A base point is an actual morphism `g : Over.mk (𝟙 S) ⟶ G.X`.
`constantPoint G g T` pulls it back to a point over any test scheme `T`
by composing the structure map `T → S`, regarded as a morphism in `Over S`,
with `g`. The lemma `constantPoint_naturality` proves that these points
commute with pullback. The proof uses associativity and the defining
commutative triangle of an `Over` morphism.

For `a : T' ⟶ T`, `constantPoint_conj_naturality` proves that conjugation
by these points is natural:

\[
g_{T'}(a^*x)g_{T'}^{-1}
  =a^*(g_Txg_T^{-1}).
\]

The proof expands `MulAut.conj`, uses preservation of multiplication and
inversion by the group-valued point functor, and substitutes the preceding
pullback identity.

`innerIso G g : G ≅ G` then applies `isoOfPoints` to the family of
multiplicative equivalences `MulAut.conj (constantPoint G g T)`.
It is an actual isomorphism in the category of group schemes, constructed
by full faithfulness of group-valued Yoneda. Its inverse and inverse laws
are supplied by the proved `isoOfPoints` construction.
The formula `comp_innerIso_hom` states its action on every test scheme:

\[
x\mathbin{\gg}\operatorname{Int}(g)=g_Txg_T^{-1}.
\]

The proof is `comp_isoOfPoints_hom` specialized to the conjugation family.
No existence of an inner scheme automorphism is assumed as input.
