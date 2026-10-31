# central-character reflection through evaluation

This internal construction uses the actual covariant functions and
right translation of `Induction.Definitions`, together with the published
uniform-character transport in `Filtration.GeneralizedEigencharacterProof`.
It introduces no literature theorem or analytic input.

Let `R` be a commutative ring, `G` a topological group, `P` a subgroup,
`sigma` a representation of `P`, and `iota : A -> P` a monoid
homomorphism whose values commute in `G` with every element of `G`.
Coefficient, group, monoid and carrier universes remain independent.

`centralEvaluation` evaluates an actual smooth induced function
at a supplied point `x`. It is an intertwiner from smooth induction
restricted along `P.subtype.comp iota` to `sigma.comp iota`. Indeed,
right translation evaluates at `x * iota(a)`; centrality rewrites this
as `iota(a) * x`, and the function's actual covariance gives
`sigma(iota(a)) (f(x))`. Linearity is inherited from the pointwise module.
The application lemma identifies its value with the published `eval`.

`eval_mem_characterSpace` uses the published intertwiner
transport to preserve the supplied common power `k` at every point.
`exists_smoothInduced_eval_ne_zero` uses extensionality of the two actual
function subtypes: a nonzero function cannot vanish everywhere.
This commutative-ring helper has a distinct name from the published
complex-only `Induction.exists_eval_ne_zero` in CompactPairingDuality,
so both APIs may occur in the same import closure.
The reflection theorem applies these two facts to a nonzero vector
from the uniform generalized character space. Its nonzero value lies
in the inducing representation's character space with exactly the
same power and character.

No field, finite dimension, admissibility, smoothness of the inducing
representation, compact quotient, character extension or spectral
decomposition is required. This proves reflection only along the
specified homomorphism with ambient central image. It does not reflect
arbitrary noncentral restrictions, extend a restricted character to a
larger centre, prove a geometric grade formula, compute a modulus, or
establish the parent whole-induction isolation and Hom comparison.
These elementary constructions and their laws introduce no analytic or spectral input.

Worker 526 implemented this construction. Workers 359 and 430 supplied
coordinate, normalization and same-power transport guidance during the
parent Hom-comparison investigation. This attribution supplies no analytic
comparison result.
