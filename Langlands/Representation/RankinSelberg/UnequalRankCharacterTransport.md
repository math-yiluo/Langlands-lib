# Unequal-rank Whittaker data under character change

This is internal derived content from `CharacterChangeBlocks`, the published
Whittaker character-change functional equivalence and right action, and the
actual coefficient sets and quotient integrands in `LocalFactor` and
`QuotientIntegrals`.

Let the small rank be n+1, the gap d=j+k+1, D the large character-change
diagonal, R the fixed right correction, and S the rectangular row scaling
constructed in `CharacterChangeBlocks`. The row scaling S is upgraded to a
continuous linear equivalence for the product topology. Each coordinate and
each inverse coordinate is multiplication by a fixed field element, so
continuity requires only a topological ring structure on the field.

The corrected large Whittaker function is

    W_new(g) = W(D g R^(-1)).

It is constructed by the published character change followed by the actual
right representation action. It transforms under the scaled additive character.
For an actual coefficient W(g)=ell(pi(g)v), the new function is the coefficient
of the transported functional ell_a and vector pi(R^(-1))v.

The image of each coefficient model is precisely the model of ell_a.
Surjectivity uses the original vector pi(R)v and cancels the inverse actions.
The same argument together with the surjectivity of the functional equivalence
proves equality between the scaled intrinsic Whittaker set and the image of the
original intrinsic set. No irreducibility, smoothness, multiplicity-one,
central-character or distinguished-functional assumption is needed.

The quotient integrand identity is

    I_old(Sx, T_a q; s) =
      |det d_a|^(s - d/2) I_new(x, q; s),

where the small inverse-character function is the published left translate and
T_a is the actual quotient translation. Its proof uses quotient induction, the
block matrix identity D M(g,x)=M(d_a g,Sx) R, cancellation of R, and
multiplicativity of the determinant weight. The half-gap shift is retained
exactly. This is a pointwise identity; it does not assert a measure law,
integrability or a rational continuation.
