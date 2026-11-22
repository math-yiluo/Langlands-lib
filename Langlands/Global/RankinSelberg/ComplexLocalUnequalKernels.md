# Quotient descent for the unequal-rank complex local kernels

The exact kernels in `ArchimedeanIntegrals` use a chosen representative of the
left unipotent coset. The representative formulas in this module hold for
every representative. Padding an upper unipotent matrix with identity
coordinates preserves its first superdiagonal sum. Left multiplication in
the leading block acts by that padding on the full rectangular point with
the rectangular variable fixed. The Whittaker characters cancel, and the
spectral weight is invariant because the unipotent determinant is one.
The same cancellation holds for fixed right translates of both Whittaker
factors, as recorded by `complexUnequalTranslatedProduct_unipotent_mul`.
In the dual kernel the Weyl inverse transpose reverses both characters,
giving the same cancellation.

Continuity follows by pulling back through the open quotient map, and
through its product with the identity on rectangular matrices for the dual
kernel. The pulled-back formulas use continuous matrix maps, smooth
Whittaker functions, and a logarithm applied to a positive determinant norm.

This internal result concerns the actual kernels of Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), §2, (2.4)–(2.5), as represented
in the Library. The continuity proofs apply at every complex spectral
parameter. Absolute convergence requires additional estimates.
