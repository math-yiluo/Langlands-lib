# Arithmetic inputs for the reductive Hasse principle over ℚ

The reduction implements Milne, *Algebraic Groups* (2017), Theorem 25.71,
printed page 565. It uses two arithmetic hypotheses. The first says that
the real completion detects triviality of finite separable cover cocycles
for simply connected groups. The second gives density of the rational points
of every torus in its real points.

The supplied quotient by the derived subgroup is identified with the
cocenter, giving a torus. Its kernel is identified with the derived group,
and smoothness of that kernel gives smoothness of the quotient. Both input
cocycles are refined to a common finite Galois cover. Twisting the group by
conjugation through the second cocycle gives a difference cocycle whose
triviality is equivalent to cohomology of the two original cocycles. The
quotient homomorphism descends to the twist with the same torus as target,
and the new kernel is simply connected by comparison over the splitting cover.

The local cohomology hypothesis makes the difference cocycle trivial at the
real place. The Hasse hypothesis on the torus makes its quotient image
globally trivial. The rational-to-real density hypothesis transfers to the
actual completion by the algebra isomorphism from ℝ. The smooth map on real
points and this density give the required quotient-point translates. The
kernel reduction then gives triviality of the difference on the Galois cover,
and fpqc reflection of cohomology returns the cochain on the original cover.
