# Standard factor choices for determinant twists at finite completions

`StandardTwistFactorChoice` packages the certified Euler polynomial and
epsilon factor of an actual determinant twist paired with a trivial
rank-one object. The equivalences refer to the given original local
representation and to the trivial character of `GL_1`. The additive
character and self-dual measure use the Library's standard factor interface.

`exists_conductorBound_standardTwistFactors` applies the formula for
highly ramified standard factors at arbitrary additive conductor. Genericity
of the original representation gives genericity of the twist. The class
certificates of the two actual objects are identified with JPSS certificates,
then transported along the two representation equivalences. Every supplied
choice at or above the conductor bound has polynomial `1` and integer
epsilon exponent given by the rank times the Tate exponent of the twist.

`standardTwistFactorChoiceAtCompletion` constructs the package from
actual finite components of two cuspidal spectral presentations and
an actual trivial rank-one component. It takes the twist equivalence
and the certified factors and identifies their additive character with
the canonical standard finite component. This records the data used in a
finite-place comparison of completed standard functional equations.

`forwardStandardTwistFactorChoice` and `dualStandardTwistFactorChoice`
read this data from a finite pair factor choice for the standard pair.
Each needs an equivalence to the twist of the given original local
component and an equivalence between the supplied rank-one component
and the trivial representation. For the dual choice, the finite data
supply the dual Euler polynomial, and existence at the canonical
self-dual measure supplies a certified dual epsilon factor.
