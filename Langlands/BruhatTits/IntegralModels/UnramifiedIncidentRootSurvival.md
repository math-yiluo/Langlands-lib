# Incident-root survival in a supplied upper unramified model

This internal construction is conditional on the Library proposition
`UnramifiedRootPositiveReductionStatement`. It does not prove that proposition,
construct the supplied integral models or tori, or prove the special-apartment
chamber theorem.

An integral section of a smooth ambient model whose generic point lies in an
original root group factors through the actual integral root model. The proof
uses `rootModel_integralPoints_eq`, naturality of integral points, and injectivity
of the ambient integral-point map.

On a singleton apartment subset, positive reduction consequently applies to every
ambient integral section with generic point in a root group. The kernel of the
actual reductive reduction is the reduction preimage of the specified unipotent
radical. Thus reduction equals the identity precisely when that generic point
has strictly positive root depth at the singleton point.

Suppose an actual zero-depth point in the original root group lies outside the
product of strict depth and the full KP doubled-root group. The neutral model is
supplied with integral points equal to the actual zero subgroup intersected with
the singleton fixer. The zero-fixer root intersection makes this point integral.
If its canonically specialized character were absent from the supplied reductive
quotient, the quotient root functor would equal its doubled functor, by the
generic relative root-system bound and the absence comparison. Perfect-residue
root lifting then supplies an integral point in the original doubled-root group
with the same quotient reduction. Their difference has trivial quotient
reduction, hence strict depth by the preceding kernel criterion. This contradicts
the depth-boundary exclusion.

The residue field of the actual maximal-unramified integer ring is algebraically
closed, hence perfect; that integer ring is Henselian. The argument retains the
actual integral torus and canonical character specialization throughout. It uses
both root lengths and the complete doubled-root subgroup, and imposes no field
or residue-characteristic restriction. `unramifiedDepthBoundaryQuotientRoot`
packages the resulting actual quotient root; its character is exactly the
specialization of the original character.

The proof is an internal composite of the named root-model image, zero-fixer,
quotient kernel, absent-root double-comparison and perfect-residue lifting
lemmas. It works entirely over the upper maximal-unramified field and requires no
downstairs building, equivariant embedding, or integral opposite-factor premise.
The positive-reduction proposition and the supplied neutral-model equality,
integral split torus, and reductive quotient remain explicit hypotheses.
