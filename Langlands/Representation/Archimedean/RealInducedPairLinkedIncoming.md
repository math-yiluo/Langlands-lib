# The incoming complex at a linked pair of real induction blocks

Write `L = d.weight.natAbs`, `M = e.weight.natAbs`,
`P = outerWeight d e k` and `H = innerWeight d e k`. For `IsLinkedAt d e k`
and `Even (P - M)`, this module constructs the incoming four-crossing map
from the actual standard module `[induced e, induced d]` to
`[induced d, induced e]`. It intertwines the compact action and every real
Lie derivative exactly. Composing it with the published `outerMap` gives
zero, so its range is contained in the kernel of that outer tail. Both
original induction-block Fourier conditions are retained in these spaces.

The construction is internal to the Library. The linked endpoint equalities
give `swapParameter e d = H + 1`, and integral arithmetic gives
`H + L + M = P`. The four unshifted recurrence parameters for the incoming
word are consequently `H`, `H + M`, `H + L` and `P`. Their unreduced parity
representatives are `L + 1`, `M + L + 2`, `0` and `M + 1`.
The assumed parity makes the first and last resonant and the middle two
generic. The helper `isGenericParameter_int` proves genericity by casting
each hypothetical singular equality to the integers and comparing parity;
it works for signed integral parameters.

The first multiplier is the explicitly defined `signedMultiplier H (L + 1)`.
It is the binomial of cutoff `H.toNat` for positive `H`, the tail of cutoff
`H.natAbs` for negative `H`, and `genericMultiplier 0` for zero `H`, always
using the reduced parity. The recurrence and symmetry follow from the
published rank-one multiplier lemmas and are transferred back to the
unreduced parity. In particular, the zero case uses the generic multiplier,
whose denominator condition follows from nonnegative real part, rather than
a binomial of cutoff zero. The two middle multipliers are obtained from
`RealInducedPairGenericSwap.exists_multiplier`; they do not vanish on their
actual parity classes. The final multiplier `lastMultiplier` is exactly
`binomialMultiplier P (((M + 1) % 2 : Nat) : Int)`.

`exists_multiplierData` packages these multipliers at the actual exponent
parameter. The published `MultiplierData.swap` recovers both final
induction-block Fourier constraints, and `swap_isRealIntertwinerModulo`
proves exact equivariance. To prove the complex identity, the last crossing's
Fourier formula multiplies each central mode by `lastMultiplier`. On the
correct parity this binomial vanishes whenever `P <= |j|`; on the other
parity the input coefficient is already zero. The published
`outerMap_eq_zero_iff` then gives `outerMap_swap_eq_zero`.
`outerMap_comp_swap` and `range_swap_le_ker` express the resulting linear-map
identity and range inclusion.

`RealInducedPairLinkedIncomingStatement` packages existence with the specified
first and last multipliers, nonvanishing of both middle multipliers, exact
intertwining, zero composite and range inclusion. No positivity assumption
on either original weight is needed. This supporting statement does not
assert that the composite incoming map is nonzero, that its range equals the
outer-tail kernel, that the outer-tail image satisfies the remaining inner
window, or that the full two-induced-block filtration has been proved.
