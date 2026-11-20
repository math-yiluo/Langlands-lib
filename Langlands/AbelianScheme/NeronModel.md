# Néron models with their generic identification

`Langlands.AbelianScheme.NeronModel` packages a commutative group scheme over
a discrete valuation ring, the existing Néron mapping-property bundle, and
an actual group-scheme isomorphism identifying its generic fibre with the
given abelian variety. `geometricSpecialPoint` uses the algebraic closure of
the residue field, and `NeronModel.geometricSpecialFibre` is pullback along
that point.

Properness and geometric connectedness of the given model combine with the
smoothness in the mapping-property bundle to give an abelian scheme.
`NeronModel.toAbelianSchemeGenericIso` uses the same generic isomorphism in
the category of abelian schemes.

## Provenance

This interface specializes the Néron model of a fixed generic scheme in
Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §1.2 and §7.4, to
abelian varieties over discrete valuation rings. It reuses the Library's
`NeronModelPropertyBundle` and group-scheme pullback.
