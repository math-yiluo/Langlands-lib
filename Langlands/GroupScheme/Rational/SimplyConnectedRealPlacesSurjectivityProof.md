# Surjectivity of localization at the real places

`simplyConnectedRealPlacesSurjectivity` proves
`SimplyConnectedRealPlacesSurjectivityStatement` in every universe. For a
simply connected group over a number field, it lifts a family of real-place
cocycles on the pullbacks of a finite separable cover to a global cocycle
on a finite separable refinement. At each real place the localized global
cocycle is cohomologous to the refined local cocycle on the same cover.

The proof applies `simplyConnectedRealPlacesSurjectivity_of_tori` to three
theorems. `realPlacesToralRepresentatives` refines the cover once for the
whole family and gives a representative in a maximal torus at each real
place. `simultaneousRealMaximalTorusApproximation` gives one global maximal
torus whose base changes are conjugate to the chosen tori by points over
the corresponding completions. `realPlacesTorusCohomologySurjectivity`
lifts the transported torus cocycles after a further finite separable
refinement. The reduction pushes the global torus cocycle into the group,
uses the local conjugators as constant cochains, and composes the two
refinements.

This is the surjectivity in Milne, *Algebraic Groups* (2017), Theorem
25.65, printed p. 563, in the finite-cover formulation of Example 2.72,
p. 61. The reduction through maximal tori follows the local representative
and approximation steps of Platonov and Rapinchuk, *Algebraic Groups and
Number Theory* (1994), Proposition 6.17, pp. 337–338, Corollary 3 to
Proposition 7.3, p. 405, and §7.3 Corollary 2, pp. 418–419.
