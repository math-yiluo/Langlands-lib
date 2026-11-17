# Finite actual geometric point kernels characterize isogenies

`geometricPointKernel A f` is the kernel of the actual homomorphism on points
of A valued in its base field. For an abelian scheme over an algebraically
closed field, `isogeny_iff_finite_geometricPointKernel` proves that this kernel
is finite if and only if f is an isogeny in the published finite-flat-surjective
sense. The result has arbitrary universe and no characteristic restriction.

For the forward implication, an isogeny has a finite actual point kernel by
the published finite-fibre theorem. For the reverse implication, the actual
scheme-theoretic kernel is closed in the proper abelian scheme and is locally
of finite type over the field. The published kernel-point equivalence gives
finitely many rational sections of that kernel scheme. The published Jacobson
argument then makes its topology discrete. Discrete fibres imply that its
structure morphism is locally quasi-finite; properness therefore makes it
finite. The published field finite-kernel isogeny theorem supplies finiteness,
flatness and surjectivity of the original endomorphism.

`natCard_geometricPointKernel_eq_zero_of_not_isogeny` applies the equivalence
contrapositively: a nonisogeny has an infinite actual point kernel, and Nat.card
of an infinite type is zero. This provides the nonisogeny half of a future
comparison with degree defined as zero off the isogeny locus.

Provenance is internal, composing actual kernel geometry, the Jacobson rational
point/discrete-topology argument, proper plus locally quasi-finite finiteness,
and the published finite-kernel isogeny theorem. It uses no Tate action,
determinant or trace comparison and asserts no geometric degree polynomiality.
