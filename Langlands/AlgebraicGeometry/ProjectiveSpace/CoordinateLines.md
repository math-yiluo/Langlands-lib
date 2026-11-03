# Actual projective coordinate lines on arbitrary schemes

Author: Worker 148.

Let `R` be any commutative ring in universe `u`, let `n` be a natural number,
and let `A = R[X_0, ..., X_n]` have its standard grading and irrelevant
homogeneous ideal `I`. Let `X` be any scheme in universe `u` with the supplied
algebra structure of `Γ(X, ⊤)` over `R`; let `j : Fin (n + 1)`.

This internal construction defines the actual morphism to polynomial projective
space associated with a coordinate basis vector, using homogeneous global
sections. It works for an arbitrary scheme with an algebra structure on its
global functions over the coefficient ring.

The basis coordinate homomorphism maps one variable to one, so the irrelevant
ideal maps to the unit ideal. `basisPoint` is the resulting actual morphism.
Its basis coordinate chart pulls back to the whole scheme.

`eq_basisPoint_iff` takes an actual ring homomorphism
`f : A → Γ(X, ⊤)`, an explicit witness `I.toIdeal.map f = ⊤`, and the
coefficient condition `f(C(r)) = algebraMap R Γ(X, ⊤) r` for every `r : R`.
The unit-ideal witness defines the global projective morphism being compared;
the coefficient condition makes its coefficient map the same as the basis
point's. Under these premises it compares that morphism with the basis point. Equality of actual morphisms implies
that the basis coordinate is a unit: its basic open is the whole scheme, so
all germs are units and the sheaf property makes it a global unit. The unit
chart equality criterion identifies the ring maps, and the coordinate-ratio
identity gives that every coordinate is this scalar times the basis vector.
Conversely, such a scalar unit makes the chart ring maps equal on all coordinate
ratios and constants, hence equal, which gives equality of actual morphisms.
The result retains nonaffine and nonreduced source schemes and compares full
scheme morphisms, rather than only their maps on points.

`basisPoint_linearAction_eq_iff` specializes this criterion to the actual
projective action of an invertible coefficient linear map
`e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)`. The irrelevant
ideal condition for the substituted coordinate map follows from invertibility.
The proved global-coordinate substitution law identifies the actual acted
morphism, and evaluating each substituted variable gives the transformed basis
vector. Thus this actual fixed-point equality is equivalent to the displayed
scalar-unit vector condition, including arbitrary scheme sources.
