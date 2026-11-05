# Dynamic compactness and finite exponents for represented parabolics

This is an internal conditional reduction for the finite-exponent part of
Renard VII.1.1. It uses the published definitions of represented-parabolic
Jacquet exponents and the finite-support argument in
`SplitComponentFiniteSupport`; it supplies no new proof of the two structural
statements appearing as its hypotheses.

`compactSpace_leftQuotient_pointImage_of_dynamic` assumes
`ParabolicDynamicStatement` and
`BruhatTits.DynamicParabolicQuotientCompactStatement`. The former provides a
rational cocharacter whose dynamic parabolic is the all-test range of the
specified parabolic inclusion. Evaluation on the identity test scheme gives
equality of that dynamic point subgroup with the literal subgroup `pointImage p`.
Rewriting by this equality identifies their `Induction.LeftQuotient` carriers
and quotient topologies. The second conclusion of the supplied compactness
statement then gives compactness of the actual quotient used by the represented
Jacquet functor. This uses the existing canonical rational-point topology
throughout; no quotient equivalence with an unverified topology is introduced.

`finite_normalizedJacquetExponents_of_dynamic_of_spanning` installs that
compactness proof and applies the finite-length-source reduction in
`SplitComponentFiniteSupport`. Besides the two structural statements, it
requires the actual normalized Jacquet characteristic spaces to span. It
concludes finiteness of the actual exponent set when the original representation
has finite length. It requires neither admissibility nor finite length of the
Jacquet module. The imported finite-support proof uses finite generation of the
Jacquet module over the actual Levi group algebra, spanning, and independence of
distinct generalized weights.

The Prop-valued
`ArbitraryParabolicFiniteSupportReductionStatement` universally quantifies this
conditional finite-support conclusion, and
`arbitraryParabolicFiniteSupport_reduction` proves it. The field and
representation-carrier universes are independent. The statement retains the
nonarchimedean local field, Hausdorff field topology, connected reductive group,
canonical ambient point topology, local compactness, nonarchimedean group, and
all parabolic, Levi, radical, multiplication-isomorphism and split-component
data. Its spanning hypothesis is precisely the supremum assertion in clause 1
of `ArbitraryParabolicExponentStatement`.

The provenance is internal: evaluating an equality of subgroup functors and
reusing an existing finite-support theorem. The original source context is
Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026,
VII.1.1, printed page 220 / PDF page 226, and V.5.1, printed page 123 /
PDF page 129. This module proves the displayed conditional reduction, rather
than the unconditional structural statements or the full VII.1.1 proposition.
Actual Jacquet spanning, parabolic realization by a cocharacter, and dynamic
quotient compactness remain prerequisites with their existing owners.
