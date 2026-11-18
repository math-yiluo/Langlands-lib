# A fixed-dimensional threshold for stable-pairing ray asymptotics

This derived module makes the power-ray asymptotic threshold explicit. For an
actual stable-pairing datum, a smooth representation satisfying `Admits`, a
good compact-open level, a fixed source vector and a fixed smooth functional,
the stable-pairing asymptotic formula holds at every inverse contracting power
whose exponent is at least the dimension of the fixed-vector space. Any upper
bound on that dimension is therefore a common threshold for all such vectors
and functionals, and for a family of actions having the same dimension bound.

The proof follows the implemented power-asymptotic argument, replacing its
unspecified kernel-vanishing power by the fixed dimension. Lift the source
Jacquet class to the stable image. The difference lies in the Jacquet kernel,
hence in some kernel of a compression power by `Admits.lower_kernel`.
Finite-dimensional kernel stabilization moves it into the kernel at the
fixed dimension, and monotonicity gives vanishing at every later power.
The compressed source and its stable lift then agree. Compression powers
equal averages of the original powers; source-class preservation and dual
invariance identify the resulting pairing with the original coefficient.

The normalized version uses the same specified modulus character and the
existing square-root normalization identity. No uniformity over all chamber
points is asserted. The good level, fixed-vector conditions, and finite
dimension bound are explicit; the field of scalars is complex and the group
and carrier universes are independent.

The contextual original source is Waldspurger, *La formule de Plancherel pour
les groupes p-adiques, d'après Harish-Chandra* (2003), Proposition I.4.3,
printed p.245, and its use in VI.2.3, printed pp.299–300, source
`waldspurger-2003-plancherel`. The dimension threshold is derived project
content; it refines the existing stable-pairing power asymptotics.
