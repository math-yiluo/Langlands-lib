# Rational extension of the division-order action

Let `K` be a nonarchimedean local field, `D` a finite-dimensional central
division algebra over `K`, and `E` an action of the actual integer order
of `D` on a finite-coordinate formal `𝒪[K]`-module `M`.
The map `rationalAction` extends `E` to a `K`-algebra homomorphism
from `D` to the existing composition algebra `K ⊗[𝒪[K]] Hom M M`.
On an integral element `a` it sends `a` to the whole tensor
`1 ⊗ E.action a`.

The rationalization of the integral action preserves the base integer
scalars by tensor balancing. Its scalar extension along `𝒪[K] → K`
then gives the algebra map via `integerTensorEquiv`. Because the integers
span `D` over `K`, algebra maps out of `D` agree whenever they agree on
the integers. Applying this criterion to the two routes of coefficient
extension proves `rationalAction_map` for every formal coefficient
algebra map.

This internal construction gives the algebra action needed to implement
the rational maps associated with division-algebra units in Drinfel'd,
*Coverings of p-adic symmetric regions* (1976), §2 A, printed p. 109.
