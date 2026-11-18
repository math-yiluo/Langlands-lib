# The chosen actual constant term at the same Jacquet fixed level

This derived module realizes a right invariant actual standard constant term
using the fixed vectors of the same normalized Jacquet module. It removes the
need to bound the rank of its coefficient tensor or the number of its summands.

First, compact averaging on the source factor of an actual coefficient tensor
is identified with compact averaging for the first coordinate of its product
action. Naturality of averaging proves the identity on pure tensors, and
linearity proves it for every tensor. The coefficient of this averaged tensor
belongs to the span of coefficients with fixed source vectors. If the original
coefficient function is right invariant at that level, averaging leaves it
unchanged. This last equality is proved at every group point by applying the
evaluation linear form to the finite orbit mean. The representation need only
be smooth.

For the standard parabolic, `standardOrdinaryJacquetObject` is the original
ordinary coinvariant quotient with its original inverse half radical modulus.
The stable pairing realizes the chosen constant term of every original
coefficient tensor in this same object's coefficient space. Tensor induction
uses the smooth functional supplied by the stable pairing, then actual
constant-term uniqueness identifies the chosen constant term. Compact
averaging therefore places a right invariant chosen constant term in the
coefficient span with source in this object's fixed space.

All structural, admissibility and stable-pairing premises are explicit.
The result concerns the original coefficient and chosen constant term on the
literal actual Levi, with independent field and carrier universes. It does
not prove orbit uniformity, the spectral root bound, or positive decay.

The contextual source is Waldspurger, *La formule de Plancherel pour les
groupes p-adiques, d'après Harish-Chandra* (2003), I.6.2 and the proof of
VI.2.3, printed pp.249–250 and 300, source `waldspurger-2003-plancherel`.
The implemented averaging and tensor comparison are derived project content
using the published compact projection and stable-pairing theorems.
