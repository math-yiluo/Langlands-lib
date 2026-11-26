# Pairing on the norm-one quotient and compact right convolution

`AdelicNormOneCuspidalPairingStatement` expresses the integral of a compact
right convolution against a test on the norm-one rational quotient as the
weighted integral of the pairings against the right translates of the input.
The group is affine, locally of finite type and connected reductive over a
number field, with a matrix representation of positive size. The kernel is
continuous and compactly supported. The input is rationally invariant,
continuous and of moderate growth. The test is rationally invariant,
continuous and rapidly decreasing in the specified adelic height on a set
meeting every rational orbit in the norm-one group.

`adelicNormOneCuspidalPairing_rightConvolution` proves absolute integrability
on the product of the quotient with the ambient adelic group. The compact
kernel support bounds the height of the right translation. At any quotient
point use a representative from the orbit cover, and use a decay exponent
of the test at least as large as the input's growth exponent. This gives a
uniform bound by a constant times the absolute value of the kernel. The
norm-one quotient has finite Haar measure, so Fubini applies. Rational
invariance and the open quotient map give joint continuity of the integrand.
The same quotient descent gives `memLp_normOneRationalRestriction`, which
puts a continuous invariant function bounded on the cover in every `Lᵖ`.

This supplies the integral exchange in the compact-convolution argument of
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
I.3.4, p. 46, using the norm-one pairing from Bernstein–Lapid, *On the
meromorphic continuation of Eisenstein series* (2024), (6.8), p. 202.
