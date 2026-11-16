# Finite coefficient reduction of reductive monomorphisms

Worker 700. This internal proposition states a conditional reduction between
two already published closed-immersion assertions.

`ReductiveMonomorphismNoetherianReductionStatement` assumes explicitly:

- `Descent.FiniteCoefficient.HomGeneralStatement`, descent of homomorphisms
  from smooth affine groups to separated finitely presented groups over
  finitely generated coefficient subalgebras;
- the scheme-level finite coefficient `MonomorphismStatement`, descent of
  monicity for the finite presentation objects in its stated scope;
- `DirectLimitReductiveStatement`, reductivity over directed colimits of rings.

Under these three premises, the closed-immersion assertion for monomorphisms
from reductive groups over locally noetherian bases is equivalent to
`ReductiveMonomorphismClosedImmersionStatement` over arbitrary schemes.
All universes agree with the original assertions, and the arbitrary-base
assertion has no added hypotheses. The target group is required only to be
separated and finitely presented.

The intended forward reduction uses simultaneous finite coefficient models
over the noetherian prime subring on affine base charts, followed by base
change and locality of closed immersions. The converse is restriction to
locally noetherian bases. This module states the reduction and proves none
of the three premises or either closed-immersion assertion.
