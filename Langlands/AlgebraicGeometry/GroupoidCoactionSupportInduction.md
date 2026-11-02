# Noetherian support induction for coaction vanishing

This internal helper isolates the induction used in the acyclicity proof.
It assumes the existing ring-relation and coaction definitions unchanged.
Rings have arbitrary universe `u`; coefficient modules have independent
arbitrary universe `v`.

`FiniteCoactionVanishing` means degree-one vanishing for every finite
coefficient coaction. `HasFiniteSupportVanishingStep` says that each such
coaction vanishes provided finite modules annihilated by some nonzero
invariant ideal have vanishing. This latter predicate is an input to the
induction step; this module does not construct the generic evaluation map
which will establish it for an effective finite cover.

`finiteCoactionVanishing_of_quotients` proves finite-coefficient vanishing
from two hypotheses: the support step over a reduced nonzero base, and
finite-coefficient vanishing on every quotient by a nonzero invariant
ideal. In the reduced case, quotient vanishing gives the required
finite-annihilator vanishing by the scalar-change reflection theorem.
For a nonreduced base, its nonzero nilradical is invariant, since the
radical of any invariant ideal is invariant over a Noetherian étale
relation. The nilradical lies in the radical of every module
annihilator. The existing ideal-power dévissage therefore applies.
Over the zero ring, every module and coefficient tensor is zero.

`noetherian_quotient_induction` is a general ring induction principle.
For any property of commutative rings in universe `u`, if the property
holds for a Noetherian ring whenever it holds for all its quotients by
nonzero ideals, then it holds for every Noetherian ring. The proof fixes
an original Noetherian ring `B` and inducts on kernels of all surjections
from `B`, using the ascending chain condition on ideals. Taking a
nonzero quotient strictly increases the kernel: comap along a
surjective ring map is an order embedding. Quantifying over all
surjective images avoids requiring a separate ring-isomorphism
invariance hypothesis for the property.

Finally, `oneCohomologyVanishes_of_finiteCoactionVanishing` uses the
existing exhaustion by finite stable submodules to remove coefficient
finiteness. These statements leave closure of the geometric covering
data under invariant quotients and the reduced generic support step
as explicit obligations.

The provenance is internal: the proofs combine Mathlib's Noetherian
ascending chain condition and ideal correspondence with the Library
radical-invariance, quotient scalar-change reflection, ideal-power
dévissage, and finite-subcoaction exhaustion theorems. No geometric
affine-descent conclusion is assumed.
