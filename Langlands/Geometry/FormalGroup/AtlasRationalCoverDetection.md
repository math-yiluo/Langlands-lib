# Finite-cover detection for whole rational formal atlas maps

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p. 109 (PDF p. 3), takes formal groups in the local sense and uses their whole rational Hom for quasi-isogenies. This pair supplies a derived comparison principle for the actual principal atlases in the Library.

For integral atlas maps, equality on the canonical localizations of a principal subcover implies equality on every original test. On a further test, localize the coefficients at the subcover generators and transfer the equality from each of those charts to the original chart by the actual transition isomorphisms. The resulting generators span the unit ideal, so coefficientwise Zariski detection gives equality of the full formal series.

`RationalHom.principalChartEvaluation` tensor-extends these integral evaluations and collects the original rational chart evaluations. If the chosen subcover is finite and the field of rational coefficients is flat over the scalar ring, the integral injection remains injective after tensoring, and tensoring commutes with the finite product of test Homs. The chart evaluations therefore detect equality in the whole original rational tensor. An arbitrary principal atlas admits a finite spanning subcover because a finite linear combination of its generators already gives one.
