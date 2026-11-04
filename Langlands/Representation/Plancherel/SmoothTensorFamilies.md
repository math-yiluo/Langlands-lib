# Finite smooth families and diagonal tensor invariants

Author: Worker 200.

This derived algebraic construction is a prerequisite for Waldspurger VI.1,
printed pp.295–296 (PDF pp.61–62), especially the diagonal invariant tensor
description on p.296. It concerns actual functions on a finite product of unit
circles with values in an arbitrary complex vector space. The coefficient
representation remains arbitrary and can be nontrivial. The actual
product-induced representation adapter is separate.

The scalar smoothness predicate is the published
`IsSmoothFiniteTorusFunction`: the real-angle lift along `finiteTorusExp` is
infinitely differentiable over the reals. The new
`smoothFiniteTorusFunctions J` is the complex subalgebra of precisely these
functions. Constants, sums and products have smooth lifts.

For any complex vector space `V`, `smoothTensorEvaluation J V` evaluates
`f tensor v` as the actual function `z ↦ f(z) • v`. Its linearity follows
from the bilinearity of scalar multiplication. No topology, norm,
finite-dimensionality or completeness of `V` is assumed.

The injectivity proof uses an arbitrary algebraic basis of `V`. The scalar
function at each basis coordinate of a tensor is the corresponding coordinate
functional applied to its vector-valued evaluation; this is proved by tensor
induction. Equality of evaluations therefore implies equality of all scalar
coordinate functions and then equality of the tensors. The basis is used
only in the proof.

`finiteSmoothFamilies J V` is the submodule spanned by the actual functions
`z ↦ f(z) • v`. `range_smoothTensorEvaluation` identifies this submodule with
the range of tensor evaluation. `mem_finiteSmoothFamilies_iff` proves the
equivalent finite-sum characterization

\[
 F(z)=\sum_{i<n} f_i(z)v_i .
\]

The forward implication expands an algebraic tensor into finitely many pure
tensors; the reverse implication evaluates that finite tensor sum.
`smoothTensorFamilyEquiv` is the resulting linear equivalence with actual
finite smooth functions, and its evaluation formula retains the same
underlying function.

For an arbitrary group `S`, a homomorphism
`τ : S →* (J → Circle)` and a representation `ρ` on `V`, the representation
`smoothTorusTranslation` is

\[
 (s\cdot f)(z)=f(z\,\tau(s)^{-1}).
\]

The published scalar translation theorem proves preservation of smoothness.
The pointwise group laws prove the representation laws.
`smoothTensorRepresentation` tensors this translation representation with
the supplied coefficient representation `ρ`. Tensor induction proves

\[
 \operatorname{ev}(s\cdot t)(z)
 =\rho(s)\operatorname{ev}(t)(z\,\tau(s)^{-1}).
\]

Injectivity of evaluation identifies diagonal invariance with the covariance
law

\[
 F(z\,\tau(s))=\rho(s)F(z).
\]

`finiteSmoothEquivariantFamilies` consists of actual finite smooth functions
satisfying this law. Its linear closure follows from the linearity of `ρ`.
`smoothTensorInvariantEvaluation` restricts evaluation to invariant tensors.
It is injective by faithful evaluation and surjective by the range theorem
and the covariance characterization.
`smoothTensorInvariantFamilyEquiv` is this concrete linear equivalence,
with its pointwise formula. Neither finiteness of `S` nor injectivity of
`τ` is required.

These are internal derived algebraic results, not a claim that arbitrary
vector-valued smooth functions have a finite tensor expansion under an
unspecified topology. The finite smooth condition is explicitly the finite
scalar-vector sum condition above, as required by the algebraic tensor
description being constructed. Comparison with locally convex or manifold
definitions of vector-valued smoothness is not established here. The source's
actual inducing spaces, canonical representative transports, unitary
self-twist stabilizer, and coefficient action require their existing
constructions and a separate adapter. Orbit descent for all representatives,
intertwiners, wave packets, spectral finiteness and Plancherel remain separate
obligations.
