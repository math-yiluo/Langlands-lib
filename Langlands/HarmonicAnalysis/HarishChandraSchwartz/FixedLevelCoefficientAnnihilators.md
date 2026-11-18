# Uniform split annihilators for finite sums of fixed-level coefficients

This derived module connects uniform Jacquet fixed-space dimension bounds to
the uniform split annihilators of the existing weak and positive parts. It
allows arbitrary finite sums of coefficients and arbitrary linear forms; no
bound on their number is assumed.

`coefficientSpaceFrom J W` is the span of coefficients of the same action `J`
whose source vectors belong to `W`. Restrict the component action to a finite
dimensional stable `W`. Its nonzero simultaneous generalized eigenspaces form
an independent family, so there are at most `dim W` exponent labels. Every
label occurs on an unchanged nonzero vector of `W`. Decompose each coefficient
source vector using these labels. The same labels serve all finite sums of
coefficients from `W`; span induction adds and scales the corresponding
eigenfunctions.

The generalized eigenvector order at each component element is bounded by
`dim W`, using stabilization of kernels of powers. The coefficient identity
transports this equation to right translations on functions. Applying the
variable-label annihilator construction to a family of such spaces with
dimensions bounded by `d` gives weak and positive monic annihilators of fixed
degree `d*d`. The weak roots have modulus one. The positive roots satisfy the
supplied uniform bound below one.

The field of scalars is complex, while the acting group, carrier, component
group and parameter universes are independent. The spectral root bound and
the membership in these coefficient spaces are explicit intermediate
hypotheses; this module does not claim the final actual orbit decay theorem.

This is an internal linear-algebra adapter for the fixed-level exponent
polynomials in Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra* (2003), I.3 and VI.2.1–VI.2.3, printed
p.243 and pp.297–300, source `waldspurger-2003-plancherel`. Its implemented
proof uses simultaneous generalized eigenspace decomposition, independent
subspaces, bounded nilpotence, coefficient right translations and the
variable-support polynomial construction.
