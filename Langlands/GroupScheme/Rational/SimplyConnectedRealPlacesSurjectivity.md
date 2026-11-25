# Reduction of real-place surjectivity to tori

`SimplyConnectedRealPlacesSurjectivityStatement` is the surjectivity clause of
the Library's real-place comparison. It uses `Cocycle.Cohomologous` to express
the twist on the common cover. The three premises of
`simplyConnectedRealPlacesSurjectivity_of_tori` are explicit propositions.

- `RealPlacesToralRepresentativesStatement` asks for a common finite separable
  refinement of the global cover and, at each real place, a cocycle of a
  maximal torus whose image is cohomologous to the refined local cocycle.
- `SimultaneousRealMaximalTorusApproximationStatement` asks for one maximal
  torus over the number field whose base change at each real place is conjugate
  to the prescribed maximal torus by a point over that completion. The
  equality of homomorphisms records this conjugacy for the actual inclusions.
- `RealPlacesTorusCohomologySurjectivityStatement` asks for real-place
  surjectivity for a torus in the same finite separable cover formulation.

The Lean proof pulls the local torus cocycles back through the isomorphisms
from the conjugacy data. Torus surjectivity supplies a global torus cocycle
after a further finite separable refinement. Pushing it forward along the
global inclusion commutes with base change. Conjugation by a point over
the completion is a twist by the constant cochain obtained from its inverse.
The proof composes the three cohomology relations and the two maps of field
covers to produce the refinement required by the statement.

This is a derived formulation of the assembly in V. Platonov and
A. Rapinchuk, *Algebraic Groups and Number Theory* (1994), Proposition 6.17,
printed pp. 337–338. The local representative step is in that proof.
Simultaneous maximal-torus approximation is Corollary 3 to Proposition 7.3,
p. 405. Torus localization is Corollary 2 in §7.3, pp. 418–419. The book
uses Galois cohomology classes. The cover and refinement data here follow
the Library's formulation of Milne, *Algebraic Groups* (2017), Theorem 25.65,
p. 563, and Example 2.72, p. 61.
