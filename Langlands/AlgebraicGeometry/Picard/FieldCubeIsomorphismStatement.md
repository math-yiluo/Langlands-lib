# The two-line-bundle isomorphism form of the geometric theorem of the cube

`Langlands.AlgebraicGeometry.Picard.FieldCubeIsomorphismStatement.{u}` is a
Prop-valued definition stating a two-line-bundle corollary of the geometric
theorem of the cube. This file states the corollary; it does not prove it.

## Exact statement

For every field `K : Type u`, put `S = Spec (CommRingCat.of K)` and take
`X Y Z : Over S`. Each structure morphism is smooth, proper and geometrically
connected. The statement explicitly quantifies over all nine hypotheses,
in the same order as `FieldCubeTrivialityStatement`, and over actual sections
`x₀ : Over.mk (𝟙 S) ⟶ X`, `y₀ : Over.mk (𝟙 S) ⟶ Y`, and
`z₀ : Over.mk (𝟙 S) ⟶ Z`. These are specified `K`-rational points.
The universe parameter `u` is arbitrary.

Let `P = X ⨯ (Y ⨯ Z)`, the chosen categorical product in `Over S`, and take
any two actual line bundles `L M : LineBundle P.left`. A line bundle here is
the Library's module sheaf locally free of rank one, with underlying sheaf
`L.obj` or `M.obj`. The imported face morphisms have the following domains
and coordinates in `P`:

| Imported face | Domain | Coordinates |
| --- | --- | --- |
| `CubeFace.first X Y Z x₀` | `Y ⨯ Z` | `(x₀, (y, z))` |
| `CubeFace.second X Y Z y₀` | `X ⨯ Z` | `(x, (y₀, z))` |
| `CubeFace.third X Y Z z₀` | `X ⨯ Y` | `(x, (y, z₀))` |

The fixed coordinate is obtained by composing the domain's unique map to
`Over.mk (𝟙 S)` with the specified section. These are actual morphisms of
schemes over `S`, constructed using the existing product projections and
lifts. Their definitions are imported unchanged from
`FieldCubeTrivialityStatement`.

For each face `i`, the hypothesis is
`Nonempty ((Scheme.Modules.pullback i.left).obj L.obj ≅
(Scheme.Modules.pullback i.left).obj M.obj)`.
Thus each comparison is an actual isomorphism of module sheaves on that
face, asserted to exist without choosing a witness. The conclusion is
`Nonempty (L.obj ≅ M.obj)`, an actual isomorphism of module sheaves on
`P.left`. There is no compatibility condition between the three chosen
face isomorphisms and no assertion that a resulting global isomorphism
must extend particular witnesses.

The only geometric hypotheses are the ones just listed. In particular,
the proposition takes neither a tensor inverse nor a global comparison
as input. It assumes no Picard-class identity, cube theorem, projectivity,
ampleness, algebraic closure or restriction on the characteristic. It
constructs no Picard group.

## Internal derived provenance and proof obligation

Milne's Theorem 6.1, on printed/PDF page 8 of the corrected author version
of *Abelian Varieties*, explicitly states the triviality of one invertible
sheaf on a product of three complete varieties when its restrictions to
the three pointed faces are trivial. It does not explicitly state this
two-line-bundle comparison. The present proposition is an internal
corollary with the following ordinary mathematical derivation.

Choose a tensor inverse `N` of `M`. The bundle `L ⊗ N` is again a line
bundle. Along each face, pullback compatibility with tensor products
transports the assumed comparison of the restrictions of `L` and `M`
to a trivialization of the restriction of `L ⊗ N`: it is isomorphic to
the restriction of `M ⊗ N`, hence to the structure sheaf. Apply the
geometric cube theorem to deduce `L ⊗ N ≅ O_P`. Tensor with `M` and
use symmetry, associativity and the inverse and unit isomorphisms to
obtain `L ≅ M`. An existential tensor inverse suffices; it is not
additional data or a hypothesis of the statement.

This paragraph explains provenance in ordinary mathematics. The Lean
file supplies no proof of invertibility, tensor or pullback compatibility,
cancellation, or the geometric cube theorem. Those results must be
proved and published before they can be used in the separate exact-target
proof of this proposition. No pending result is assumed as an instance.

The source's conventions on printed/PDF page 2 require a variety to be
separated of finite type and geometrically integral. The geometric
hypotheses here agree exactly with the imported
`FieldCubeTrivialityStatement`. As explained in its companion Markdown,
properness supplies separatedness, finite type and completeness;
smoothness supplies geometric regularity; and geometric connectedness,
together with the specified section, makes the regular scheme after
extension to an algebraic closure nonempty and connected. Its irreducible
components are disjoint and open, so there is a single component; regularity
also gives reducedness. Hence these are nonsingular complete varieties
in Milne's conventions. This source comparison is not a formal proof of
these geometric implications.

The intended balanced cube application compares two tensor products by
their three face restrictions, then pulls back the resulting isomorphism.
Neither the concrete balanced face identities nor that application is
established by this statement.

## Sources and errata

- Original underlying theorem: J. S. Milne, *Abelian Varieties*, the
  corrected January 2, 2022 author version of the 1986 *Arithmetic
  Geometry* chapter, Theorem 6.1, printed/PDF p.8; conventions p.2.
  Registered source `milne-abelian-varieties-1986-author-2022`,
  SHA256 `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
  Retained file:
  `literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
  [Author PDF](https://www.jmilne.org/math/xnotes/AVs.pdf).
- The complete [author errata page](https://www.jmilne.org/math/articles/1986b.html)
  was read. It says the listed corrections are incorporated into the
  corrected author version; none of its entries changes Theorem 6.1.
  Registered snapshot `milne-abelian-varieties-1986-errata-2026-10-25`,
  SHA256 `e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`.
  Retained file:
  `literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`.
