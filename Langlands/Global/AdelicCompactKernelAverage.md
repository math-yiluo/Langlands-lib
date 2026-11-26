# Compact averaging of adelic test kernels

Let \(K\) be a compact subgroup of the infinite adelic point group, viewed
inside the full adelic group. For a continuous weight \(a\) on \(K\), the two
averages of a kernel \(h\) are
\[
 L_a h(x)=\int_K a(k)h(k^{-1}x)\,dk,\qquad
 R_a h(x)=\int_K a(k)h(xk)\,dk.
\]
These use the supplied finite measure. The two averages preserve smooth
compact test functions. For the left average, smoothness on an infinite
slice follows by compact parameter integration of a jointly smooth
kernel. The finite-adelic invariances follow from commutation of the
infinite and finite factors. The support is contained in the product of
the compact subgroup with the original support. Inversion converts the
right average into a left average.

When the measure is left invariant, the left translate space of \(L_a h\)
is an image of the left translate space of \(a\). The same bound holds for
the right translate space of \(R_a h\). Also \(L_a\) preserves right
compact finiteness of \(h\), since right translation acts on the input to
the linear averaging map. The proofs pass through finite spans of
continuous functions, so the linearity of all the integrals applies.

The right convolution identities use compact-support Fubini and
substitution in the ambient Haar integral. Left averaging of the kernel
averages the output of convolution evaluated at \(xk\). Right averaging
of the kernel averages the input at \(yk^{-1}\) before convolving.
Right invariance of the ambient Haar measure along the compact subgroup
justifies the second substitution.

These are the averaging identities for the compact factors in the
approximate identity of Mœglin–Waldspurger, *Spectral Decomposition and
Eisenstein Series*, I.4.5, printed p. 61
(`moeglin-waldspurger-1995-spectral-decomposition`, collection fingerprint
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`,
chapter `05.4_pp_49_77_Upper_bounds_as_functions_of_the_constant_term.pdf`,
SHA-256 `a72fe12ffc7707cc35e91375a8fc9dc62c35570afbbb061c0e7ff6db99a90d3d`).
