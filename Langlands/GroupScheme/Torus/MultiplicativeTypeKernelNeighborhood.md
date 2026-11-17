# Identifying multiplicative-type kernels near a fibre using a supplied quotient

Worker 879. Internal conditional step in the relative kernel proof.

Suppose `i : N → H` is a monomorphism of group schemes and `q : H → Q`
is a supplied affine fppf quotient whose full scheme-theoretic kernel
is the full point-functor range of `i`. Let `f : H → G` kill `i`,
and assume `N` and `Q` are of relative multiplicative type.
At a base point `s`, suppose the actual fibre kernel of `f` equals
the full range of the fibre of `i`.

With **an explicit premise** proving
`MultiplicativeTypeMonomorphismSpreadingStatement`, separatedness of `G`,
and a locally noetherian base or locally finitely presented `G`,
`exists_neighborhood` produces an open neighborhood `U` of `s`
where the full kernel of `f_U` equals the range of `i_U`.
It also proves that this actual kernel is of multiplicative type.
`neighborhood` chooses the resulting open subset. The module does not
prove the monomorphism-spreading statement or the main kernel criterion.

The implemented proof first shows that `f` kills the full kernel of `q`
using its equality with the supplied subgroup range. Published fpqc
homomorphism descent constructs `v : Q → G` with `q ≫ v = f`.
On the fibre at `s`, the equality of full kernels and the published
`FpqcHomDescent.mono_of_kernel_range_le` show that `v_s` is monic.
The explicit spreading premise gives an open neighborhood where `v`
is monic. On that neighborhood, monomorphic postcomposition preserves
the full kernel range. The actual kernel is therefore isomorphic to
`N_U` by the published `KernelRepresentative.iso`, and relative
multiplicative type transports through that isomorphism.

This is derived content using existing Library descent, kernel and
base-change constructions. It is not a new transcription of an
unproved literature result. The relative geometry/locality helper is
another contribution of the same task and remains subject to its own
independent review.
