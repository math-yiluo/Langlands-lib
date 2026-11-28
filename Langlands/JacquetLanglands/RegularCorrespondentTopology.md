# Continuous local choices of regular elliptic correspondents

Let `K` be a field with a topological ring structure and `A` a finite-dimensional
central simple `K`-algebra with its module topology. The lemma
`Langlands.CentralSimple.continuous_reducedCharpoly_coeff_units` computes
reduced characteristic polynomial coefficients in a finite Galois splitting
chart. The chart on the units is continuous for the module topologies. A
continuous linear retraction from the splitting field onto `K` recovers the
original coefficient from the chart coefficient.

Let `F` be a characteristic-zero nonarchimedean local field and `D` a
finite-dimensional central division `F`-algebra with its module topology.
The group `Dˣ` carries the units topology. The lemma
`Langlands.JacquetLanglands.isOpen_regularDivisionUnits` takes the preimage of
the open separable locus in the space of coefficients of monic polynomials.
`Langlands.JacquetLanglands.exists_local_regularCorrespondent` applies
`regularCoefficientSlice` with exponent one to a specified split
correspondent `γ` of `g'`. Evaluating that slice on the coefficients of the
reduced characteristic polynomial gives a continuous choice on an open
neighborhood of `g'` with value `γ` at `g'`. Equality of the characteristic
polynomials gives `Corresponds` because the reduced characteristic
polynomial of a regular division unit is separable and irreducible.

Deligne–Kazhdan–Vignéras, *Représentations des algèbres centrales simples
p-adiques*, introduction (a)–(b), printed p. 33, describes the regular
elliptic class correspondence and the regular character formula.
`Corresponds` uses the equal characteristic polynomial criterion of
Badulescu, *Correspondance de Jacquet–Langlands pour les corps locaux de
caractéristique non nulle* (2002), §1, p. 695. The local choice uses the
coefficient chart in `Langlands.BaseChange.RegularCoefficientSlice`.
