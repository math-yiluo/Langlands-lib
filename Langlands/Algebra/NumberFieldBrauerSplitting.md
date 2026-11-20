# Splitting central simple algebras over number fields

`Langlands.Brauer.NumberFieldBrauerSplittingStatement` says that a
finite-dimensional central simple algebra over a number field splits
if its scalar extension to each finite and infinite completion
splits. Splitting means the existence of an algebra isomorphism with
a matrix algebra of positive size.

The proof chooses a finite Galois matrix splitting and takes the
relative unit-cohomology class of its scalar factor set. At a finite
place, `unitsLocalMap_relativeClass` identifies its localization with
the class of the matrix chart extended to that completion. The two
cochain maps agree because they restrict along the same decomposition
homomorphism and include coefficients into the same completed field.
A split algebra has zero relative class.

At an infinite place of the splitting field with a nontrivial
stabilizer, its generator is complex conjugation. The proof lifts
it to the completed complex field and transports the factor set
there. Splitting makes that factor set a coboundary. The product of
its values at \((c,c)\) and \((1,1)\) is therefore a complex norm
and gives sign invariant zero. A trivial stabilizer gives invariant
zero directly.

The finite and infinite vanishing hypotheses now give zero global
relative class by the Library's unit-cohomology Hasse principle.
The comparison with actual matrix splitting gives the required
global chart.

This is the splitting consequence of the injectivity assertion
in Platonov and Rapinchuk, *Algebraic Groups and Number Theory*
(1994), §1.5.1, Theorem 1.12, p. 38. It supplies the splitting
criterion used in the reduced-norm theorem.
