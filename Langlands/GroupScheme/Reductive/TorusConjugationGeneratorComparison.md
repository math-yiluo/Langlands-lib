# Generator comparisons with a torus conjugate over algebras

This internal derived adapter uses the actual homomorphism
`torusConjugateAlgebraHom` from `RelativeTorusConjugationRigidity`.

`TorusConjugatesOnRoot` is the proposition that conjugation holds for all points
of one supplied map from the additive group, on every scheme test and every
refinement to the parameter scheme. The supplied additive-group map need not
be a root parametrization.

`torusConjugateAlgebraHom_root` assumes this proposition and proves equality of
the corresponding actual root restrictions over every commutative algebra and every algebra
point of the parameter scheme. The proof transports root points through
`baseChangePointsEquiv`, applies the conjugated homomorphism's evaluation
formula and the supplied equation, and uses extensionality of maps from the
additive group.

`torusConjugateAlgebraHom_comp` assumes that the restriction of a homomorphism
along a supplied group map factors through the commutative group containing
the conjugating point. After every algebra base change, conjugating the
homomorphism fixes that restriction. The proof evaluates on all scheme tests,
uses the supplied factorization, and computes inside the commutative group of
points. The supplied group itself need not be a torus.

`torusConjugateAlgebraHom_torus` specializes this to the canonical coordinate
torus map over the algebra. The equality retains the original pulled-back
homomorphism on the right, so any supplied common torus square can be used
without choosing a new coordinate torus map.

The base ring and its algebras may have nilpotents and need not be local. The
parameter scheme need not be affine. No reductivity, finiteness, root-datum
existence or existence of conjugating points is asserted or assumed by these
transport lemmas. Their provenance is the imported base-change point and root
transport identities, the evaluation of inner conjugation, and commutativity
of the supplied target group; no external source is used.
