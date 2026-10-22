# Ideal-adic sheaf systems

Author: Worker 13.

The input is a genuine Grothendieck site `(C, J)`, a commutative coefficient
ring `R`, and an ideal `I`. The displayed Mathlib sheafification instances are
required for the indicated module categories. This module uses the existing
category of sheaves and its natural-transformation morphisms.

`quotientCoefficients` constructs a sheaf with coefficients in `R / I` by
taking the quotient of each section module and sheafifying. The original
restriction maps descend because module maps preserve ideal multiples.
The quotient presheaf is not presumed to be a sheaf.

`sheafifyEndofunctor` packages sectionwise application followed by
sheafification as a functor of module endofunctors. Applied to the accompanying
module inverse system, it gives `powers` and `functor`: actual sheaf reductions
at every ideal power, with compatible natural transition maps. The canonical
map from a sheaf to each reduction uses the inverse sheafification counit
and the quotient map on sections. Its compatibility with transitions is proved.

`constantSystemFunctor` separately sheafifies the constant presheaves on the
module reductions. No unproved identification of this system with the
reductions of an arbitrary local system is asserted. `inverseLimit` and
`projection` use the categorical limit in the category of module-valued
sheaves; this is an ordinary inverse limit, not a derived inverse limit.
Transport through the constructed functor gives algebraic monoid actions on
the whole inverse system. Each monoid element acts by a sheaf endomorphism
over the fixed site. When the acting monoid is a group, these operators are
automorphisms, with inverse given by the inverse group element. Smooth
equivariance for a group moving the underlying analytic space remains a
separate construction.

This is a derived sheaf-theoretic infrastructure for the inverse coefficient
systems in Harris, *Galois properties of cohomological automorphic forms on
GL(n)*, J. Math. Kyoto Univ. 39-2 (1999), pp.307-308 and p.311, the paragraph
preceding Proposition 4.10. Worker 13 read these original pages. The stable
lattice, continuous group action, descent to the required lisse sheaf,
Mittag-Leffler conditions, and comparison with derived cohomology remain
separate constructions or theorem obligations. An arbitrary sheaf is not
declared to have those properties.

Source ID:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`;
PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
member
`Harris (1999), Galois properties of cohomological automorphic forms on GL(n).pdf`.

The formal dependencies are the accompanying
`Langlands.Coefficients.AdicSystem` and pinned Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, particularly
module sheaves, constant sheaves, sheafification and limits. Object, morphism,
ring, module and action universes are explicit. No project axiom or
cohomology-output assumption is introduced.
