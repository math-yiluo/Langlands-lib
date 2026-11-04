# Finite-Galois descent of split unipotence from stable vector subgroups

This internal derived construction proves finite-Galois descent of a represented
split Ga-series for smooth connected affine unipotent groups. The exact
`SplitUnipotentStableVectorSubgroupStatement` remains an explicit structural
premise. This module does not prove that statement or maximal-torus conjugacy.

The nontrivial central subgroup step applies the supplied stable-vector theorem
over the extension field, with the group acting on itself by conjugation. The
natural vector coordinates identify its central subgroup with a standard vector
group of positive dimension. The previously constructed scalar Galois norm and
its smooth connected image then give a nontrivial central split subgroup over
the base field. Faithfully flat base change reflects triviality on all tests,
so a nontrivial ground-field group supplies the required nontrivial extension
input.

Strong induction on the actual ground-field Lie dimension finishes descent.
The trivial all-test group has a split series of length zero. In the other case,
take the nontrivial smooth connected central split subgroup just constructed.
The published normal-subgroup quotient theorem produces a smooth affine fppf
quotient, which is connected because the projection is surjective. The nontrivial
connected kernel strictly decreases actual Lie dimension. Over the extension
field, the quotient is a smooth affine surjective image of the supplied split
group, hence split. Unipotence passes to the quotient in the existing
representation-theoretic convention. Induction makes that quotient split over
the base field. Extension closure of represented split series combines its
series with the kernel series.

`finiteGaloisSplitSeriesOfStableVector` retains a finite length and the actual
`HasSplitSeries` witness returned by this argument. The field universe is
unrestricted, and all characteristics, finite fields and imperfect fields are
retained. No subgroup-of-split-implies-split assertion, rational-point
surjectivity, or division by the extension degree is used. The provenance is
the explicit composition of the imported constructions and dimension induction.
