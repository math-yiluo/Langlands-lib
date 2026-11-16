# Extending relative maximal tori through a central product

This is an internal derived construction for the relative maximal-torus part
of the derived-group correspondence. Let `G` and `D` be reductive group schemes
over any scheme `S`, let `d : D ⟶ G` be closed, and let `z : Z ⟶ G` be central
with `Z` a relative torus. Assume the multiplication `Z ⊗ D ⟶ G` is a central
isogeny. Given a closed relative torus `a : A ⟶ D` maximal on every residue
fibre, `RelativeDerivedTorus.exists_extension` constructs a closed relative
torus `t : T ⟶ G` maximal on every residue fibre and an isogeny
`e : Z ⊗ A ⟶ T` whose composite with `t` is multiplication in `G`. It also proves
that the range of the full scheme-theoretic intersection `D ×_G T ⟶ D` equals
the range of `a` on every test scheme. The definition
`RelativeDerivedTorus.extensionModel` chooses this torus, its inclusion and
the isogeny, retaining all these properties.

The extension is the smooth closed all-test centralizer of `a ≫ d`, supplied
by `relativeTorusCentralizer_hasSmoothClosedRepresentative`. Monicity of `d`
and relative maximal-torus self-centralization identify its full intersection
with `D` as the range of `a`. The central-product reconstruction theorem
`exists_centralIsogeny_of_intersection_range_eq` gives a central isogeny
from `Z ⊗ A` onto this centralizer.

The supporting theorem `IsIsogeny.isCommMonObj_of_source` descends
commutativity through an isogeny by cancelling its epimorphic tensor square
from the multiplication identity. Products of the two commutative source
groups are commutative by the multiplicative equivalence on their points.
The theorem `IsTorus.of_isogeny_from_torus` proves that a smooth affine isogeny
image of a field torus is a torus: extend to a splitting field and apply the
published split-torus schematically dominant image theorem to the reduced
smooth target. The theorem `relativeTorus_of_smooth_isogeny_from_product`
uses this on geometric fibres to establish reductivity of the commutative
target. The commutative-reductive theorem then shows that the target is a
relative torus over the original base.

Apply these results to the centralizer and its product isogeny. The resulting
torus is self-centralizing: an element centralizing it centralizes its
subtorus `A` and hence belongs to the centralizer, while commutativity gives
the reverse inclusion. Base change and the field self-centralization
criterion prove maximality on residue fibres.

All arguments are in the arbitrary-base and arbitrary-universe setting. The
construction needs no normality or semisimplicity hypothesis on `D`, no quotient
data, and no maximality hypothesis on the central torus `Z`; the central-product
isogeny is an explicit premise. Its existence and the complete host
correspondence remain separate obligations. This internal result composes the
published centralizer, self-centralization, torus-image and central-product
theorems; it is not a separate transcription of an external source.
