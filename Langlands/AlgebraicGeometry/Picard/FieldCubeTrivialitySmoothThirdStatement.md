# The theorem of the cube over a field with a smooth, possibly non-proper third factor

`Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialitySmoothThirdStatement.{u}`
is a proposition definition stating the geometric theorem of the cube over an
arbitrary field when the first two factors are smooth, proper and geometrically
connected and the third factor is smooth and geometrically connected but **not**
assumed proper. This file states the theorem; it does not prove it.

## Exact statement

The proposition is the Library's
`Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityStatement` with exactly
one change: the hypothesis `IsProper Z.hom` is removed. Everything else, including
the order of the hypotheses, the products, the face maps and the use of
`Nonempty` of actual isomorphism types, is unchanged.

For every field `K : Type u`, let `S = Spec (CommRingCat.of K)` and let
`X Y Z : Over S`. The explicit hypotheses are, in this order:

1. `Smooth X.hom`, `IsProper X.hom`, `GeometricallyConnected X.hom`;
2. `Smooth Y.hom`, `IsProper Y.hom`, `GeometricallyConnected Y.hom`;
3. `Smooth Z.hom`, `GeometricallyConnected Z.hom`.

The points `x₀`, `y₀` and `z₀` are actual morphisms from the terminal object
`Over.mk (𝟙 S)` to `X`, `Y` and `Z`. Their underlying scheme morphisms are
sections of the structure morphisms, that is, specified `K`-rational points.

The ambient product is the chosen categorical product `P = X ⨯ (Y ⨯ Z)` in
`Over S`, an actual iterated fibre product over `S`. The three faces are the
Library's maps from
`Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityStatement`, imported and
not redefined:

| Lean map | Domain | Coordinates in `X ⨯ (Y ⨯ Z)` |
| --- | --- | --- |
| `CubeFace.first X Y Z x₀` | `Y ⨯ Z` | `(x₀, (y, z))` |
| `CubeFace.second X Y Z y₀` | `X ⨯ Z` | `(x, (y₀, z))` |
| `CubeFace.third X Y Z z₀` | `X ⨯ Y` | `(x, (y, z₀))` |

For every `L : LineBundle P.left`, suppose that the pullback of `L.obj` by
`Scheme.Modules.pullback` along the underlying scheme map of each face is
isomorphic to `Langlands.Scheme.Modules.structureSheaf` of the face's domain.
The conclusion is that `L.obj` is isomorphic to the structure-sheaf module of
`P.left`. The three hypotheses and the conclusion are `Nonempty` of actual
categorical isomorphism types; no Picard group, class identity or chosen
witness is introduced.

`LineBundle` is the Library's full subcategory of module sheaves that are
locally free of rank one, matching the sources' line bundles (invertible
sheaves). The statement assumes nothing about `Z` beyond smoothness and
geometric connectedness: no properness, quasi-compactness, separatedness,
finite type, projectivity, ampleness, algebraic closedness of `K`, restriction
on the characteristic, group structure on any factor, or prior cube, seesaw or
descent theorem.

## Relation to the proper statement

The proposition implies `FieldCubeTrivialityStatement` (in the same universe)
by forgetting the hypothesis `IsProper Z.hom`: given the data and the nine
hypotheses of the proper statement, discard `IsProper Z.hom` and apply this
proposition to the remaining eight hypotheses, the same three sections and the
same line bundle. The conclusion is literally the same.

## Original source and specialization

The main source is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian
Varieties* (preliminary version of the first chapters), Theorem (2.5), printed
page 18 (PDF page 22): let `X` and `Y` be complete varieties over `k` and let
`Z` be a connected, locally noetherian `k`-scheme; for points `x ∈ X`,
`y ∈ Y` and `z ∈ Z`, a line bundle on `X × Y × Z` whose restrictions to
`{x} × Y × Z`, `X × {y} × Z` and `X × Y × {z}` are trivial is trivial. The
field `k` is arbitrary. By the convention (0.4), printed page 1 (PDF page 5), a
variety over `k` is a separated `k`-scheme of finite type that is geometrically
integral, and a line bundle on a scheme is a locally free module of rank one.
The convention does not restate "complete", which has its usual meaning:
proper over `k`.

The present statement is a specialization of Theorem (2.5). The following is an
explanation in ordinary mathematics, not a formal proof of these comparisons.

- **`X` and `Y` are complete varieties.** As explained in the Markdown of
  `FieldCubeTrivialityStatement`: properness gives separatedness and finite
  type, and properness is completeness. Smoothness over a field makes the base
  change to an algebraic closure `K̄` regular; as it is noetherian, its
  irreducible components are disjoint, hence open. Geometric connectedness makes
  the base change connected, and the rational point makes it nonempty, so it is
  irreducible; regularity gives reducedness. Hence `X` and `Y` are geometrically
  integral, so they are complete varieties over `K`.
- **`Z` is locally noetherian.** A smooth morphism is locally of finite
  presentation, so `Z` is locally of finite type over the noetherian ring `K`,
  hence locally noetherian.
- **`Z` is connected.** Geometric connectedness says that every base change of
  `Z` to a field over `K` is connected; for the field `K` itself this is `Z`.
  (The section `z₀` also shows that `Z` is nonempty.)
- **The points.** The sections `x₀`, `y₀` and `z₀` are `K`-rational points, a
  special case of the source's arbitrary points. For a rational point `x₀`, the
  fibre `{x₀} × Y × Z` is identified with `Y × Z` through `x₀`, and the
  restriction of `L` to it is the pullback along `CubeFace.first X Y Z x₀`;
  likewise for the other two faces.

Thus every instance of the present hypotheses is an instance of Theorem (2.5),
with the products formed as iterated fibre products over `Spec K`. The present
statement is weaker than Theorem (2.5) in two respects: the third factor is
required to be smooth and geometrically connected rather than merely connected
and locally noetherian, and the points are rational. Smoothness of `Z` is kept so
that a proof through rigidity over a reduced parameter scheme (for instance via
the Picard scheme of `X`) remains available; this suffices for the intended
application, whose parameter is smooth and geometrically integral but not
proper.

J. S. Milne, *Abelian Varieties* (author's corrected January 2, 2022 version of
the 1986 *Arithmetic Geometry* chapter), Theorem 6.1, page 8, is the cube theorem
for three complete varieties with rational base points. Remark 6.3, page 9,
says that, at least when `k` is algebraically closed, it is not necessary to
assume in Theorem 6.1 that the third factor `W` is complete (Mumford 1970, §6,
p. 55), nor even that it is a variety (Mumford 1970, §10, p. 91). Milne's remark
is cited as context for dropping completeness of the third factor; the present
arbitrary-field statement rests on Edixhoven–van der Geer–Moonen
Theorem (2.5).

The product association and the `CubeFace` maps are internal categorical
implementations of the sources' three faces using Mathlib's products in the
slice category; they introduce no additional geometric result. The Lean
declaration retains all eight geometric hypotheses and all three sections
explicitly. A separate exact-target proof obligation must establish the
published proposition.

Registered sources:

- `edixhoven-vandergeer-moonen-abelian-varieties-draft`; retained file
  `literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`;
  SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`;
  locators: (0.4), printed page 1 (PDF page 5), conventions; Theorem (2.5),
  printed page 18 (PDF page 22).
- `milne-abelian-varieties-1986-author-2022`; retained file
  `literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`;
  SHA-256 `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`;
  locators: Theorem 6.1, page 8; Remark 6.3, page 9.
