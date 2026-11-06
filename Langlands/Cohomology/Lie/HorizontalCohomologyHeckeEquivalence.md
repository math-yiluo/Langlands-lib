# Original horizontal quotient equivalences and Hecke integration

This internal helper considers the existing horizontal complexes of two
actual complex Lie modules, their smooth translating-group chain actions,
and an equivariant chain equivalence. All brackets, compact equivariance,
infinitesimal insertion and chain compatibility laws remain explicit, with
independent Lie/module/group universes.

`equivCohomology_heckeAction` states that the already constructed original
quotient equivalence commutes with the two integrated Hecke actions for the
same Borel Haar measure. Its implemented proof applies
`Hecke.integratedAction_intertwiner` to that original equivalence's
underlying intertwiner, using the smoothness transferred through the two
original cycle quotients. No new cohomology model, normalization or
compatibility hypothesis is added. The provenance is internal composition
of these existing constructions; no external-source identification or
existence/nonvanishing theorem is claimed.
