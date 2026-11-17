# Assembling an anti-affine quotient from a flat affinization

`AntiAffineQuotient.ofFlatAffinization` constructs the existing
`AntiAffineQuotient G` from a supplied actual homomorphism `q : G ⟶ Q`
satisfying `IsAffinization q`. It assumes that the affine target and the full
scheme kernel are smooth and connected, and that `q` is flat, surjective and
quasi-compact. The result retains the supplied group and homomorphism exactly.
The two displayed equality lemmas are definitional equalities.

The constructor derives the remaining two fields. The supporting theorem
`IsAffinization.antiAffine_kernel` in `AntiAffineKernel` proves anti-affineness
of the full kernel using global-sections base change. The supplied projection
is smooth because its base change along itself is the projection from the
product of the source and its smooth full kernel. The published
`KernelPair.isPullback_scheme` gives this comparison, and fpqc descent of
smoothness gives the result. The auxiliary
`FpqcHomDescent.smooth_of_smooth_kernel` works over an arbitrary scheme base.

This is an internal construction in support of the smooth connected case of
SGA 3, Exposé VI_B, Theorem 12.2, printed pages 430–431 / PDF pages 100–101,
Gille–Polo recomposed edition dated 13 October 2024. Its proof of kernel
anti-affineness uses flat base change rather than the successive quotient
argument in the source. The complete Tome I errata of that date do not modify
Theorem 12.2 or Lemma 12.3. Source identifier:
`sga3-expose-vib-gille-polo-2024`, SHA-256
`88d8ccb045fc959535155eb4b0fc72e3e4845730fb73355f2043e8023b7db3d2`.

This constructor does not prove that an affinization homomorphism exists,
that it is flat or surjective, or that its full kernel is smooth and connected.
Those are separate prerequisites of `AntiAffineQuotientExistenceStatement`.
The existing predicates and quotient structure are unchanged, and all field
constructions retain an arbitrary universe parameter.
