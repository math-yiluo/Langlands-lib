# Affine orbits of a smooth action relation

`Langlands.GroupScheme.SchemeAction.SmoothActionAffineOrbitStatement.{u}`
is an unproved proposition definition for arbitrary fields and universes.
Let a smooth affine group scheme `G` act on an affine finite-type scheme
`X` over `k`. Assume that its actual action relation
`G × X → X × X`, `(g,x) ↦ (g • x,x)`, is smooth.
For every rational section `x`, the proposition asks for an actual
factorization of the published orbit morphism

`G → Q → X`.

The scheme `Q` must be affine, locally of finite type, and quasi-compact
over `k`. Its embedding `j : Q → X` must be both an open immersion and a
closed immersion. The orbit projection `q : G → Q` must be smooth,
surjective, and quasi-compact, and the equality `q ≫ j = a.orbitMap x`
must hold as scheme morphisms over `k`. In particular, the embedded
scheme has exactly the underlying image of the actual orbit morphism.
The equality and monicity of the immersion also preserve all-test orbit
fibers, including on nonreduced tests.

The field need not be algebraically closed or perfect. The group need
not be connected or reductive, and `X` is not assumed reduced or smooth.
The section is rational over the given field; the conclusion is over
that same field. No pointwise replacement of the action is made.

This is the geometric step isolated from Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), proof of Proposition
A.8.12, printed p.554 (PDF p.580). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Smoothness of the relation makes the geometric orbit morphisms smooth.
Their images are open and partition the geometric scheme, so each
orbit is also closed. An orbit of a rational section descends to a
clopen subscheme over the original field. A clopen subscheme of an
affine scheme is affine. These steps motivate the exact statement;
their scheme-theoretic construction, descent, and the listed morphism
properties remain proof obligations.

The statement supplies no cocycle-model existence or reductivity
criterion. It asks for the orbit's actual affine factorization, which
can later be combined with a known all-test stabilizer equation.
