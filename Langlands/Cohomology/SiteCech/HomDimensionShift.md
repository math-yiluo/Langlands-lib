# Dimension shifting in coefficient Hom complexes

This is an internal algebraic construction for the
coefficient dimension shift in a Cech argument. It concerns actual morphisms
in an R-linear abelian category D, where R is any ring.

Let P be a chain complex in nonnegative degrees and let S = (F -> I -> Q)
be an exact short complex whose first arrow is a monomorphism. Fix a
nonnegative integer n. Assume that every morphism P_(n+1) -> Q lifts to I,
that Hom_R(P,F) is exact at n+2, and that Hom_R(P,I) is exact at n+1.
`exactAt_linearYonedaObj_quotient` proves that Hom_R(P,Q) is exact at n+1.
The uniform version assumes these positive exactness and lifting statements
in every positive chain degree and concludes positive exactness for Q.
`quotientCocycleBoundary` uses this result to choose a primitive of a
supplied Q-valued cocycle. Its output is a morphism P_n -> Q together with
the equation that its differential is the supplied cocycle. The choice is
noncanonical.

The proof starts with a Q-valued cocycle x in degree n+1 and chooses a lift
y to I using the explicit lifting hypothesis. Its differential factors
through F by exactness of S. This F-valued factor is a cocycle, since two
successive chain differentials compose to zero and F -> I is monic.
Exactness for F one degree higher writes the factor as a boundary d b.
Subtracting b followed by F -> I from y therefore gives an I-valued
cocycle. Exactness for I writes this corrected lift as a boundary d z.
The image of z in Q has boundary x, proving the desired exactness.

No injectivity of I, epimorphism I -> Q, exactness of P, or representable
presentation of its terms is assumed. Injectivity and chain exactness can
supply the I-coefficient hypothesis separately. Surjectivity of Hom from
P_(n+1) is retained explicitly: a sheaf epimorphism alone need not imply
it. Applying this lemma to a Cech nerve still requires a proof of the
lifting hypothesis for its actual chain objects. This is the coefficient
propagation step, not a Cech-to-derived comparison or analytic acyclicity
theorem.
