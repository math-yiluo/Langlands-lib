# The first E₆ fundamental weight in the integral root lattice

This internal root-datum calculation uses Mathlib's numbering of the E₆
Cartan matrix. For an integral root datum with all simple-coroot pairings
equal to that matrix, and whose coroots span the full cocharacter lattice,
it proves

$$
3\omega_0=4\alpha_0+3\alpha_1+5\alpha_2+
6\alpha_3+4\alpha_4+2\alpha_5.
$$

Here the roots and the fundamental weight belong to the supplied actual
integral lattices. The weight is the generic construction
`TypeANegationWeyl.firstWeight`; that construction does not require type A.
The coroot-span condition makes the simple coroots an integral basis.

The proof checks the six integer Cartan sums using kernel-checked
`decide`, then compares the pairings of both sides with every simple
coroot. The perfect pairing and the simple-coroot basis identify the
two lattice elements.

As a derived consequence, any additive map from the weight lattice to
an abelian group that vanishes on every actual root sends this
fundamental weight to an element killed by three. This is an algebraic
implication for a supplied map. It neither constructs a Tits obstruction
nor asserts a comparison with an anisotropic kernel or a Brauer class.
The coefficients and proof are derived directly from the published
Cartan matrix and integral weight APIs.
