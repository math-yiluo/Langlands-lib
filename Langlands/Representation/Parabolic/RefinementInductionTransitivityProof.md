# Natural normalized induction transitivity for block refinements

Author: Worker 162.

`Langlands.Parabolic.normalizedRefinementInductionTransitivity` proves exactly
`NormalizedRefinementInductionTransitivityClause.{uF,uV} F T B S` from
`RefinementTransitivityStatement`. It constructs a natural isomorphism
from `T.normalizedRefinedInductionFunctor B S` followed by
`T.normalizedParabolicInductionFunctor B` to
`T.normalizedComposedInductionFunctor B S`.

The field universe `uF` and representation-carrier universe `uV` are independent.
The theorem quantifies over every prime, p-adic field, compatible topological
data, block shape and refinement. It imposes no positive ambient-rank condition,
so it includes the empty/rank-zero cases of the published statement. The
statement and its imports are preserved.

## Implemented maps and proof

Write `G = GL_n(F)`, `M = B.Levi F.Carrier`, `Q` for the actual refined
parabolic in `M`, and `s = B.leviEmbedding F.Carrier`. Write `a` for
`T.leviHalfModulus B` and `b` for `T.refinedLeviHalfModulus B S`.
All scalar characters have values in the units of the complex numbers.

The forward map sends an iterated induced function `H` to
`g ↦ H(g)(1)`. Its covariance follows by outer covariance, then inner
covariance, using the established identity that the composed half modulus
on a preimage element is `a` of its outer projection times `b` of its
composite projection. A single open right stabilizer of `H` also stabilizes
the forward function.

The inverse sends a direct induced function `f` to

`g ↦ [m ↦ a(m)⁻¹ • f(s(m) * g)]`.

The helper `direct_section` computes direct covariance along the embedding
of `Q`. The product formula for the half modulus cancels the outer scalar
and proves covariance of each inner function. To prove its smoothness,
choose an open right stabilizer `K` of the entire function `f`. For fixed
`g`, pull `K` back through the continuous homomorphism
`m ↦ g⁻¹ * s(m) * g` and intersect with the open kernel of `a`.
This open subgroup fixes the inner function at every argument `m`,
including its scalar factor.

The helper `direct_outer` uses the actual outer unipotent part of a
parabolic element `q`. This part embeds in the composed parabolic and
has trivial composite Levi projection. Direct covariance therefore gives
`f(q * g) = f(s(projection(q)) * g)`.
Applying this identity to `s(m) * q` proves outer covariance of the
inverse, after the character identity
`a(m)⁻¹ = a(projection(q)) * a(m * projection(q))⁻¹`.
The original subgroup `K` stabilizes the whole outer inverse function:
the equality holds at every `g` and every `m`.

Forward evaluation is linear and commutes with right translation.
Evaluating the inverse at `m = 1` proves one inverse identity; outer
covariance along `s(m)` and cancellation of `a(m)` prove the other.
The resulting `Representation.Equiv` includes an invertible linear map
and intertwining; in particular the inverse is linear and equivariant.
`SmoothRep.mkIso` packages these equivalences and `NatIso.ofComponents`
uses pointwise postcomposition to prove naturality for every morphism.
The final two clauses are the prescribed evaluation formulas, by
construction. All helpers are private to the proof module.

## Provenance and scope

The original is Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Printed pages 444–446 (PDF pages 5–7) were read directly: section 1.8
specifies positive-half covariance, right translation and one open
stabilizer; Proposition 1.9(c), page 445, states smooth induction in
stages with compatible normalizing factors; section 2.2 and Proposition
2.3(c), page 446, specialize to ordered block refinements.

The explicit evaluation formulas and stabilizer construction above are
the implemented derivation for the Library's concrete presentations.
The proof uses its already constructed determinant half-modulus identities.
It proves smooth induction transitivity alone, with no admissibility,
finite length or irreducibility assumptions. It does not assert compact
induction comparison, a Haar-modulus identification, Jacquet transitivity,
or a comparison with a flattened block shape.
