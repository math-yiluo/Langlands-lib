# Actual integral maps underlying rational abelian-scheme isomorphisms

This internal supporting construction specializes the algebraic localization
argument in `Langlands.CategoryTheory.RationalizationDenominators` to the actual
category of abelian schemes over an arbitrary scheme. Its base-change argument
uses the existing additive pullback functor and its extension to rational Hom
groups in `Langlands.AbelianScheme.RationalBaseChange`.

For actual abelian schemes `A` and `B` over `S` and a rational isomorphism
`e : Rationalization.of A ≅ Rationalization.of B`, `RationalIsoIntegralData e`
is the generic integral-representative data. `rationalIsoIntegralData e`
constructs it without an additional premise. The data consists of nonzero
integers `a`, `b` and actual abelian-scheme homomorphisms `f : A ⟶ B` and
`g : B ⟶ A`, with

- `Rationalization.ofHom f = a • e.hom`;
- `Rationalization.ofHom g = b • e.inv`;
- `f ≫ g = (a * b) • 𝟙 A`;
- `g ≫ f = (a * b) • 𝟙 B`.

The last two identities hold in the actual integral category. The generic
construction proves them by clearing both rational denominators and then
annihilating the two discrepancies using the localization equality criterion.
It does not require a theorem that abelian-scheme Hom groups are torsion free.

For any actual map `b : S' ⟶ S`, `RationalIsoIntegralData.baseChange d b`
transports supplied data `d` to data for the actual rational isomorphism
`rationalBaseChangeIso b e`. The two integers are retained. The actual maps
are exactly the pullbacks of the supplied maps. Compatibility of rational
pullback with integral inclusion and additivity give the rational image
equations. Functoriality, additivity and preservation of identities give both
exact integral composite equations. The four `baseChange_*` lemmas expose
these unchanged denominators and the actual pulled-back maps.

No flatness or finiteness condition on `b` is imposed. This construction does
not assert that the independent noncomputable choice `rationalIsoIntegralData`
commutes with base change; it constructs transport of supplied witnesses.

The unit supplies an algebraic part of comparing rational and integral moduli
descriptions. It proves no finite-flat isogeny property, subgroup quotient,
integral order action, Rosati or polarization comparison, level comparison,
moduli representability, smoothness, admissibility or projectivity. Those are
separate obligations of the normalized Harris CM representability task.
