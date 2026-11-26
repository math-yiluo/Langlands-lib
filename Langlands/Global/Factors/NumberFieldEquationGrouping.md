# Grouping number-field Euler families along the restriction of places

`NumberFieldEquationGroupingStatement` groups the local factors of a finite family of upper-field functional equations at the actual places of a base number field. Given a finite base set of removed finite places, each upper equation uses every finite place over that set together with every infinite place. The grouped family satisfies the same engine inputs over the base. The base field, extension field, and indexing type have independent universes.

`numberFieldEquationGrouping` expands the upper exceptional set as the preimage of the base exceptional set. The finite fibres are the actual finite places lying over each base place, and the infinite fibres are the infinite places with that restriction. The proof multiplies the upper equations on a common right half-plane, then groups the local factors and Euler products fibre by fibre. `numberFieldProductFactors_finite` gives the finite-place formulas for the ordinary, dual, and gamma factors of the grouped family.

This is the finite-place regrouping of the product of Rankin–Selberg functional equations used in Henniart and Herb, *Automorphic induction for GL(n) (over local non-archimedean fields)* (1995), Lemma 8.13 and §§8.14–8.16. The equation inputs remain hypotheses.
