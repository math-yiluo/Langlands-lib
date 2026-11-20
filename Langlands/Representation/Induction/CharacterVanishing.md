# Character vanishing for proper parabolic induction

`ProperParabolicCharacterVanishingStatement` gives character value zero at every regular elliptic element for actual normalized induction from a standard block parabolic with at least two blocks and admissible inducing data. This is the ordinary character vanishing used in Henniart–Lemaire (2011), II.4.8, printed p. 91, from the induced character formula in II.4.5, printed pp. 86–88.

The proof computes the trace at a compact open level where the test function is bi-invariant. The fixed vectors of the smooth induction are a finite product of fixed spaces indexed by double cosets. For a section on one double coset, a group element can contribute to its diagonal block only if it belongs to a conjugate of the inducing subgroup times the level subgroup. Right invariance and vanishing on those conjugates then make every diagonal contribution zero. Finite sampling implements this calculation for the actual integrated operator.

With a closed inducing subgroup and compact left quotient, the conjugacy saturation is closed. It is the projection of the closed relation of points fixed by right translation on the quotient. Its open complement gives a neighbourhood on which the distribution has local value zero. A regular elliptic matrix lies outside the conjugates of a proper block parabolic because a block upper triangular characteristic polynomial factors into the positive-degree characteristic polynomials of its diagonal blocks.

The normalized induction uses the actual Levi inflation and half-modulus twist. Their published admissibility results and compactness of the parabolic quotient put it in the compact-quotient character calculation.
