# Local nontriviality from the adelic multiplication pairing

Worker 1692, internal derived support for the Hecke global functional equation.
The module assumes an actual group homeomorphism from the additive adele group,
written using `Multiplicative`, to its full compact-open Pontryagin dual. Its
evaluation must be the actual multiplication pairing associated to the supplied
global additive character. Existence of this equivalence is an explicit
hypothesis and is not proved here.

Multiplying an adele supported at one finite or infinite place by any adele
keeps it supported at that place. The module proves these coordinate identities
using the actual product and restricted-product operations. It also defines the
infinite additive restriction and proves its continuity.

Injectivity of the supplied pairing detects zero: if `psi(a*x)` is one for every
adele `x`, the character associated to `a` equals that associated to zero.
If a local restriction were trivial, apply this observation to the adele whose
chosen coordinate is one and whose other coordinates are zero. Its product
with every adele has trivial character value. This would make the single-place
adele zero, contradicting its coordinate one. The argument applies to every
finite and infinite completion and preserves arbitrary universe.

The final theorem combines the proved finite local nontriviality with the
published finite additive-component construction and self-dual Haar existence.
It delivers exactly the finite local-data existential in the global target,
under the same explicit pairing hypothesis. No diagonal-triviality theorem,
adelic self-duality, almost-everywhere conductor assertion or global functional
equation is asserted by this supporting unit.
