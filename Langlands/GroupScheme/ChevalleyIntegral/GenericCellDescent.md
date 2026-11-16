# Descent of the generic ordered cell

This internal construction concerns supplied integral Chevalley data over a
commutative domain `R` with fraction field `K`. The root datum is reduced and
its character lattice is finitely generated. It does not assume a reductive
integral realization.

`genericSchemeProjection` is the projection from the generic fibre of any
scheme over `Spec R`, regarded as a morphism over `Spec R`. When the scheme is
flat over `R`, this projection is schematically dominant by flat base change
of the generic-point inclusion.

Suppose `W` is flat over `R`, its generic fibre maps flatly to a supplied
Chevalley group over `K`, and `W` maps to the integral ambient matrix cell.
Assume the generic matrix map agrees with the restriction of this ambient
map. The ambient base-change construction lifts its generic point to the
ambient cell over `K`, with the same matrix. The field intersection theorem
then factors the generic map through the full ordered root and torus
parameter scheme. Parameter restriction gives a map over the original base
from the generic fibre. Its composite with the closed integral parameter
inclusion is the generic restriction of the original ambient map; this
follows by composing with the monomorphic ambient matrix cell and using
both base-change identities. Schematic dominance and the closed-immersion
factorization lemma descend that map to `W`.

`genericOrderedCellFactor` chooses the resulting actual integral parameter
map, and `genericOrderedCellFactor_comp` proves its factorization identity.
The torus factor is the diagonalizable group of the entire character lattice.
All content is derived from the Library's flat schematic descent, field cell
factorization and explicit parameter and ambient base-change constructions.
Identification of an open cell in the integral closure and smoothness of
that closure remain subsequent obligations.
