# Tangent vectors fixed by a whole torus

For a commutative group scheme `T`, an affine group scheme `G` over any
commutative ring `R`, and a homomorphism `i : T → G`, containment of the
all-test range of `i` in `Lie.elementCentralizer G X` is equivalent to
`X` having zero adjoint weight for `i`. The forward proof tests the
containment at each affine coefficient algebra. The reverse proof
pulls a point of `T` back to that algebra and uses the equivalence
between constant-point commutation and the adjoint fixed-vector equation.

When `T` is affine, the published zero-weight comparison identifies this
condition with `X ∈ Lie.torusCentralizerLie i`. This is a statement about
the whole subgroup functor, including nonaffine and nonreduced test
schemes, rather than only points over fields.

Given a representative `j : C → G` of `torusCentralizer i`,
`Lie.torusCentralizerTangentFactor i j hrep X hX` is the canonical
actual dual-number tangent vector in `C` lifting `X`. It is constructed
by applying the representative's point equivalence to the dual-number
point `X`. Monicity of `j` reflects reduction to the identity, so this
lift lies in `lieKernel C R`. Its image under `Lie.targetMap j R` is
exactly `X`. Neither `C` nor `G` is assumed smooth, and no semisimplicity
or maximality assumption is used.

This is a derived all-test adapter for the Lie-centralizer step used in
Milne, *Algebraic Groups* (2017), Proposition 17.90, printed p.381 /
PDF p.397, where Proposition 10.31 is invoked to put `X` in the Lie
algebra of the centralizer of a maximal torus. The proof here uses
actual dual-number kernels and the existing zero-weight comparison.
It does not prove that a semisimple vector lies in the Lie algebra of
the torus itself, or supply the nilpotent structure or unipotent
quotient arguments used later in that proposition.
