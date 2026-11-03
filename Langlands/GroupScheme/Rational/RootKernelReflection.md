# Integral reflections from full-kernel-centralizing representatives

This internal assembly constructs the integral part of actual relative-root
reflection data from supplied rational normalizing representatives. It does
not prove that those representatives exist intrinsically. The exact target
`RelativeRootReflectionExistenceStatement` retains that geometric obligation.

For an actual split torus over an arbitrary field, a nonzero character `a`,
and a normalizing rational point `n`, assume that `n` sends `a` to `-a` under
the actual Weyl action and centralizes the full scheme-theoretic kernel of
`a` on all test schemes and refinements. The underlying scheme map of the
torus inclusion is monomorphic. Then
`IsSplitTorus.existsUnique_coroot_of_mem_kernelCentralizer` gives a unique
actual cocharacter with self-pairing two and the reflection formula on every
character. It first invokes
`exists_integral_difference_of_mem_kernelCentralizer` from
[`RootKernelDivisibility`](RootKernelDivisibility.md), and then applies
`IsSplitTorus.existsUnique_coroot_of_integral_difference` from
[`IntegralCoroot`](IntegralCoroot.md). Thus integrality is proved from full
kernel centralization, rather than assumed. The result does not require
primitivity of `a` or smoothness of its kernel.

When the ambient group scheme is affine over the field,
`RelativeRootReflectionData.ofKernelCentralizingRepresentatives` applies
that unique-coroot theorem separately to each actual relative root. Each
root is nonzero by its defining membership condition. Classical choice
selects the actual cocharacter, while its self-pairing and action laws are
the two conclusions of the theorem. The representative family is preserved
definitionally by the structure construction.

`exists_reflectionData_of_kernelCentralizing_representatives` also permits
the normalizing points to be supplied existentially for each actual root.
Choice first selects the representative family, and the preceding
construction supplies reflection data whose representatives retain the
given full-kernel centralization. This works with an empty root set as
well. No finiteness, reductivity, connectedness, maximality, primitive-root,
or characteristic restriction is used in the assembly.

The provenance is an internal composition of the actual full-kernel
descent construction authored by Workers 1335 and 1339 and the integral
coroot extraction authored by Worker 1225. It finishes the algebraic
assembly after the quotient-factorization step in Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), C.2.15 Step 2, printed
pp.604–605 (PDF pp.630–631), registered source
`conrad-gabber-prasad-2015-pseudo-reductive`. The geometric representative
and root-flip hypotheses remain explicit; this helper supplies neither
an intrinsic normalizer construction nor a proof of the unrestricted
reflection-existence statement.
