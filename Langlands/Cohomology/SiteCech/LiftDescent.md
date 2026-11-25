# Descent of a local lift using degree-one Hom exactness

This internal construction is a categorical form of the
degree-one Cech obstruction argument. It uses actual morphisms in an abelian
category and Mathlib's exact-complex lift and descent operations.

Let D be an R-linear abelian category, with R a ring, and let P be a chain
complex in nonnegative degrees. Let epsilon: P_0 -> A be an epimorphism with
d_1 epsilon = 0, and assume P_1 -> P_0 -> A is exact. Let
S = (F -> I -> Q) be an exact short complex whose first arrow is a
monomorphism. A target map s: A -> Q has a supplied local lift
t: P_0 -> I, meaning t followed by I -> Q equals epsilon followed by s.
Finally assume the linear Hom cochain complex Hom_R(P,F) is exact in degree
one.

`liftObstruction` factors d_1 followed by t through F, using exactness of S
and the fact that this composite is killed by I -> Q. Its composite with
F -> I is d_1 t. Precomposition with d_2 kills it, since d_2 d_1 = 0 and
F -> I is a monomorphism. Thus it is an actual degree-one Hom cocycle.
This construction and its two identities need only the abelian structure;
the linear structure enters the Hom-complex exactness argument.

`exists_correctedLocalLift` uses exactness in Hom degree one to express that
obstruction as d_1 followed by some b: P_0 -> F. Subtracting b followed by
F -> I from t gives t' with d_1 t' = 0, and t' has the same image in Q.
`liftByCechExactness` descends t' along epsilon, using exactness at P_0.
Its output includes the equation that the resulting A -> I lifts s.
Cancellation of the epimorphism epsilon proves that equation.

The construction does not assume that I is injective or that I -> Q is
an epimorphism. It applies to any augmented chain complex with the stated
degree-zero exactness and degree-one coefficient exactness. No category
of geometric objects, representability, cover, finite nerve presentation,
or sheafification is supplied here. For a free sheaf Cech nerve these
conditions and the supplied local lift must be established separately.
This is the first descent step toward a dimension-shifting comparison,
not a proof of a Cech-to-derived criterion or analytic acyclicity.
