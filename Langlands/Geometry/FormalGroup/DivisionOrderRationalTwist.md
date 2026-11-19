# Quasi-isogenies for division-unit twists

For a finite-coordinate formal `𝒪[K]`-module over an `𝒪[K]`-algebra,
let `E` be an action of the actual integer order in a finite-dimensional
central division `K`-algebra `D`. For a unit `g : Dˣ`, `twistQuasiIsogeny`
constructs a full-order quasi-isogeny from `E` to `twist K D E g`.
The forward map is the rational action of `g⁻¹`, and the inverse is the
rational action of `g`, as elements of the whole tensor Hom.

The multiplicativity of `rationalAction` gives both inverse equations.
On each integer `a`, the order action on the target is the action of
`g⁻¹ a g`. Forward equivariance is the image under `rationalAction` of
the identity `g⁻¹ a = (g⁻¹ a g) g⁻¹`. Equivariance of the inverse follows
from the existing upgrade of a quasi-isogeny with equivariant forward
map. The complete quasi-isogeny commutes with coefficient extension.
For an integer-order unit it agrees with the rationalization of the
existing integral `twistUnitIso`.

This is the division-unit map to the conjugated target that occurs in
the action formula of Drinfel'd, *Coverings of p-adic symmetric regions*
(1976), §2 A, printed p. 109. The construction uses the algebraic
conjugation part of that formula for any finite-dimensional central
division algebra over `K`. The effect on the height of a framing and
the Frobenius correction in the action formula require further results.
