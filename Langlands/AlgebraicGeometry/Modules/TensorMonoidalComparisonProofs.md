# Localized tensor unitors and symmetry

Worker 339 proves `Langlands.Scheme.Modules.tensorMonoidalComparison` with
exact type `TensorMonoidalComparisonStatement.{u}`. The theorem has no
additional hypotheses and applies to every scheme in universe `u`. Its three
constituents are also exported as `tensorMonoidalLeftUnitorComparison`,
`tensorMonoidalRightUnitorComparison`, and `tensorMonoidalSymmetryComparison`.

For `X : Scheme`, write `F = sheafify X` and let `c_M : F(M.val) ≅ M` be the
component of `sheafifyForgetIso X`. The fixed `localizedTensorIso X M N`
first tensors `c_M.inv` and `c_N.inv`, then applies the tensorator of `F`.
The explicit unitors apply `F` to the presheaf unitors and then apply `c_M`;
the explicit swap is `F` applied to the presheaf braiding. These are the
published maps, with the directions fixed in the statement.

The proof uses three private categorical lemmas. For a lax monoidal functor
`F` and an isomorphism `c : F(P) ≅ M`, `leftUnitor_comparison` proves that
the tensor of the unit map `ε` with `c.inv`, followed by the tensorator,
`F` of the left unitor, and `c.hom`, is the left unitor of `M`. It expands
the tensor of morphisms into whiskerings and applies the lax monoidal
left-unitality equation. Left-unitor naturality then moves `c.inv` past the
unitor, and `c.inv ≫ c.hom = 𝟙 M` finishes the calculation.
`rightUnitor_comparison` uses the corresponding right-unitality and
right-unitor naturality equations, with the other order of whiskerings.

For a lax braided functor, `braiding_comparison` proves the analogous square
for any `c : F(P) ≅ M` and `d : F(Q) ≅ N`. It applies the braided functor
law to the tensorator followed by `F` of the braiding, and then uses
braiding naturality for `c.inv` and `d.inv`.

Each exported law applies its private lemma directly to `sheafify X` and
the counit components. The published `sheafifyMonoidal` and
`sheafifyBraided` instances supply the required functor laws. In particular,
the unit map `Functor.LaxMonoidal.ε (sheafify X)` is definitionally the
inverse of `sheafifyTensorUnitIso X`, hence the counit inverse at
`structureSheaf X`. The tensorator is definitionally the hom of the
localization comparison used in `localizedTensorIso`. Thus these
specializations prove the precise fixed equations without auxiliary
identifications or replacement maps. The final theorem combines the left,
right, and symmetry laws in the published conjunction order.

This is an internal categorical proof from the published `Tensor`,
`TensorMonoidal`, and `TensorMonoidalComparisonStatements` modules and
Mathlib's monoidal and braided functor laws. It does not claim a separate
translation of an original literature theorem. The proof changes no
imported files and assumes no geometric restriction, comparison law, or
monoidal structure on pullback. Pullback compatibility and its strong
symmetric monoidal assembly are outside this theorem's scope.
