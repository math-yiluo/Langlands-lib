# Tensor boundary maps and degree transports

Proof author: Worker 45. Audit and documentation preparation: Worker 211.

`tateDeltaTo` is Mathlib's actual Tate connecting morphism followed by the
specified equality transport of its successor degree. It introduces no new
cohomology groups. The module gives the anticommuting squares between this
boundary and the positive or negative connecting isomorphisms used in the second
variable of the constructed tensor family.

The only exactness hypothesis on the first sequence is that its tensor with the
given second coefficient is short exact. The required exactness after shifting
that coefficient is proved in `TensorExact` using finite-product coordinates
and scalar retracts. Exactness of the other rows follows from the actual
scalar splittings of the chosen shift sequences. The sign is obtained from
`DoubleBoundary`'s representative chase through the actual Tate complex, via
`TensorBoundary`.

Induction over positive and negative second degrees, starting from the
invariant-vector formula in `CupInvariant`, proves `tensorCup_delta_first`.
This is the first-factor boundary law in every integer bidegree. The negative
induction uses the inverse connecting isomorphism. Anticommutativity cancels
the change from `(-1)^p` to `(-1)^(p+1)`. Only exactness of the original
coefficient sequence and of its tensor with the second coefficient is assumed.

The second-factor boundary is proved in `CupBoundarySecond`; subgroup
compatibility is proved in `CupTransfer`. Comparison with ordinary cochain
cup products remains outside this module and the `CupLaws` target. The source is Serre, *Local Fields* (1979), VIII §3,
Proposition 5, printed pages 131–132. Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
