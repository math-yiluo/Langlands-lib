# Compact convolution: bilinearity, Dirac laws and mixed associativity

Worker 150, Task 5394. Source: Renard, French version of 9 July 2026,
II.3.10, printed pp.50–51 / PDF pp.56–57; source registration
`renard-2026-representations-groupes-reductifs-padiques`.

This proof unit targets the exact published `BilinearUnitStatement`,
`DiracStatement` and `MixedAssociativityStatement`, with the full group universe.
Bilinearity follows from the existing bilinear compact-support pairing and the
iterated evaluation formula. The pairing with the actual Dirac distribution is
point evaluation: a test representative on its singleton support proves this.
The Dirac translation laws then use the published original left/right actions;
the right action has inverse parameter. At the identity they give both unit laws.

The three mixed associativity laws hold for every locally constant scalar
function. The first uses the extended convolution evaluation formula and
inversion of a product. The middle and last also use the extended Fubini law
from the preceding algebra proof unit. Bundled smooth intermediate functions
have exactly the published test-kernel values by the regularity comparison.
All helper constructions are internal consequences of the existing pairing
and kernel definitions and do not replace the convolution operation.
