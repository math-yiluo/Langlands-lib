# Naturality of the full-piece identification

This internal supporting lemma is derived for a proof of Renard,
*Représentations des groupes réductifs p-adiques* (2026 version), VI.10.4,
second Lemma (`ℨ_Ω ⊂ ℨ_D`) and its consequence, printed p.211 / PDF p.217.
After that Lemma Renard filters `r_P i_P(Π_D)` by the geometric lemma and
identifies its successive quotients with the twists `w · Π_D`, `w ∈ W(D)`.
He then uses the action of `R_D = End(Π_D)` on these quotients "par
fonctorialité". That requires the identification of a piece with a twist
to be compatible with endomorphisms of `Π_D`. Renard leaves this
compatibility implicit, so it is not a separately numbered statement in
the source.

Let `D` be an actual `GeometricLemmaIntersectionDatum` whose two
intersection parabolic maps `D.p'` and `D.q'` are isomorphisms. The Library
then supplies `D.fullPieceEquiv σ`, a linear equivalence from the piece
`D.pieceFunctor.obj σ` onto `σ` that intertwines the actions through the
recovered Levi conjugacy (`Exponents/ActualGeometricFullPiece`).

`GeometricLemmaIntersectionDatum.fullPieceEquiv_naturality` states that
this equivalence is natural in `σ`. For every morphism `a : σ ⟶ σ'` of
smooth representations of `M(F)` and every vector `y` of the piece of `σ`,

`D.fullPieceEquiv σ' ((D.pieceFunctor.map a) y) = a (D.fullPieceEquiv σ y)`.

The definition `GeometricLemmaIntersectionDatum.naturalFullPieceEquiv`
packages the whole family `σ ↦ D.fullPieceEquiv σ` together with this
naturality, as an element of the subtype of families of piece
identifications that commute with every morphism `a : σ ⟶ σ'`. Its value is
`D.fullPieceEquiv` itself (`naturalFullPieceEquiv_val`, by `rfl`); it adds
no new data, only the naturality proof. It is the declaration under review.

## Proof

`D.fullPieceEquiv σ y` is, by definition, the full-parabolic Jacquet
class-to-vector equivalence applied to `y(1)`, the value of the induced
function at the identity. The piece functor's map acts on induced functions
pointwise, through the Jacquet functor's map. So both sides are values of
the Jacquet class-to-vector equivalences at Jacquet classes, and the
statement reduces to `eJ'(J(a) w) = a(eJ w)` for a class `w` of the
Jacquet module of `σ`. The proof writes `w` as the class of a vector `x`
(`Jacquet.Localization.mk_surjective`). The Jacquet map sends that class to
the class of `a x`, and `fullParabolicLeviJacquetEquiv_mk` evaluates both
sides to `a x`.
