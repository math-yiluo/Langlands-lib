# Actual CM pullback on the stable automorphic operator core

Worker 2. This internal construction restricts the actual CM argument pullback
from `CMOperatorConjugation` and `AutomorphicCMTransport` to the existing
stable automorphic core. It introduces no new original-literature
identification or preservation assumption.

For every actual CM number field `K : Type uK` and natural rank `n`, including
zero, let `C` denote `finiteSmoothComplexConj n` and let `c_A` denote the
proved involution of the concrete generated operator algebra. The core
condition for `f` is that `A f` is automorphic for every operator `A` in this
algebra. The proved identity

\[
A(Cf)=C((c_A A)f)
\]

and actual automorphic-form preservation prove core preservation.
Involutivity proves reflection. The resulting submodule image equality
constructs `StableAutomorphicFunctions.complexConj` by restricting the
existing continuous complex-linear equivalence. It retains the inherited
subtype topology and fixes complex values.

The restricted map is involutive, with itself as inverse. Whole-algebra
covariance and its finite, standard infinite compact and genuine enveloping
specializations descend by the faithful subtype inclusion. The finite and
compact parameters transform by the actual arithmetic CM matrix maps; the
enveloping parameter transforms by the existing complex algebra
`ArchimedeanLieTransport.envelopingEquiv` induced by the CM field involution.
Inclusion into the full automorphic form space agrees with its CM pullback.
Forward and inverse evaluation are both `f(g) ↦ f(c(g))`.

No compactness of the additive adele quotient is required. The construction
does not identify the core with all automorphic forms or prove that it is
nonzero. Actual CM images of invariant subspaces, their irreducibility and
their isomorphism-class transports are subsequent constructions.
