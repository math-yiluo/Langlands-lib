# Jacquet evaluation of the right Lie derivative along one exponent line

Fix the inducing list at parameter \(p\) and a compact-finite standard
vector there. Move one radial exponent by \(z\) and retain the vector's
unitary profile. At each group argument the canonical Jacquet value of
its right Lie derivative at the new parameter is entire in \(z\).

`continuedJacquet_shiftedLie_apply` gives the formula used for this
holomorphy. The exponent-shift equivalence on the standard module acts
by a scalar function that is one on the unitary subgroup. It therefore
agrees with compact-profile transfer. After transport back to the
original standard module, the Lie operator is affine in \(z\). The
constant term is the original Lie operator. The linear term is the
transported operator at shift one minus the original operator. Applying
canonical Jacquet evaluation to these two fixed vectors gives two
fixed-profile families, with the second multiplied by \(z\). Their
pointwise holomorphy gives the conclusion.

This is an internal consequence of the Library's exponent deformation and
Jacquet continuation, with the latter based on Jacquet, *Archimedean
Rankin–Selberg integrals* (2009), §7.2, Proposition 7.2 on printed p. 48.
