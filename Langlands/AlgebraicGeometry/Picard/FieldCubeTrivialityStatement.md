# The geometric theorem of the cube over an arbitrary field

`Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityStatement.{u}` is a
proposition definition stating the geometric theorem of the cube for smooth
proper geometrically connected pointed schemes over an arbitrary field.
This file states the theorem; it does not prove it.

## Exact statement

For every field `K : Type u`, let `S = Spec (CommRingCat.of K)` and let
`X Y Z : Over S`. Each of the three structure morphisms is assumed smooth,
proper, and geometrically connected. The points `x₀`, `y₀`, and `z₀` are
actual morphisms from `Over.mk (𝟙 S)` to `X`, `Y`, and `Z`, respectively.
Thus their underlying scheme morphisms are sections of the corresponding
structure morphisms, equivalently specified `K`-rational points.

The ambient product is the chosen categorical product `P = X ⨯ (Y ⨯ Z)`
in `Over S`, hence an actual iterated fibre product over `S`. The three
maps are constructed from the existing product projections and lifts:

| Lean map | Domain | Coordinates in `X ⨯ (Y ⨯ Z)` |
| --- | --- | --- |
| `CubeFace.first X Y Z x₀` | `Y ⨯ Z` | `(x₀, (y, z))` |
| `CubeFace.second X Y Z y₀` | `X ⨯ Z` | `(x, (y₀, z))` |
| `CubeFace.third X Y Z z₀` | `X ⨯ Y` | `(x, (y, z₀))` |

Here the fixed coordinate means the composite of the domain's unique map
to the terminal object `Over.mk (𝟙 S)` with the specified section. The
coordinate descriptions express morphisms of schemes and do not reduce
the construction to their action on rational points. These three helpers
are defined for any base scheme; the theorem statement itself quantifies
only over spectra of fields.

For every `L : LineBundle P.left`, suppose each pullback of `L.obj` by
`Scheme.Modules.pullback` along the underlying scheme map of one of these
faces is isomorphic to `Langlands.Scheme.Modules.structureSheaf` of its
domain. The conclusion is an isomorphism of `L.obj` with the structure-sheaf
module of `P.left`. All three hypotheses and the conclusion use `Nonempty`
of actual categorical isomorphism types. They assert existence without
choosing witnesses or introducing a Picard group or a class identity.

`LineBundle` is the Library's full subcategory of actual module sheaves
locally free of rank one. The structure-sheaf module is the Library's
`Langlands.Scheme.Modules.structureSheaf`, which is defined using
`SheafOfModules.unit`. The statement assumes no group structure on the
schemes, projectivity, ampleness, algebraic closedness, restriction on
characteristic, or prior cube, seesaw, or descent theorem.

## Original source and specialization

The source is J. S. Milne, *Abelian Varieties*, the author's corrected
January 2, 2022 version of the 1986 *Arithmetic Geometry* chapter,
Theorem 6.1, printed/PDF page 8. That theorem treats complete varieties
over an arbitrary ground field with three rational base points and an
invertible sheaf trivial on the three corresponding faces.

The conventions on printed/PDF page 2 define a variety as a separated
scheme of finite type that is geometrically integral, and nonsingularity
by geometric regularity. The present statement specializes the source to
smooth proper geometrically connected schemes. In the usual mathematical
comparison, properness gives separatedness and finite type, and smoothness
over a field gives geometric regularity. After extension to an algebraic
closure, the scheme is regular and noetherian, and its irreducible
components are disjoint and open. Geometric connectedness therefore
forces a single component; the specified rational point also ensures
nonemptiness after base change. Regularity gives reducedness, so the
scheme is geometrically integral. Properness supplies completeness.
Consequently these hypotheses give nonsingular complete varieties in
Milne's conventions, a specialization of his theorem.

This paragraph explains source correspondence in ordinary mathematics.
It is not a formal proof of these comparisons or of the cube theorem.
In particular the Lean declaration retains all nine geometric hypotheses
and all three sections explicitly; it does not replace them by a
stronger implicit theorem or assume global triviality of the bundle.

The product association and the `CubeFace` definitions are internal
categorical implementations of Milne's three displayed faces, using
Mathlib's existing products in the slice category. They introduce no
additional geometric result. A separate exact-target proof obligation
must establish the published proposition.

Registered source: `milne-abelian-varieties-1986-author-2022`.
Retained file: `literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
SHA-256: `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Locators: page 2, conventions; page 8, Theorem 6.1.
Original: [Milne, Abelian Varieties](https://www.jmilne.org/math/xnotes/AVs.pdf).
