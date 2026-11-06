# Actual finite-level stabilizers from locally constant finite orbits

This module constructs an actual open subgroup fixing a continuous
rational-invariant function, from local constancy of its finite slices
and finite dimensionality of its orbit under a specified open subgroup
of the actual finite adelic point group. When the specified subgroup is
compact, the constructed subgroup is also compact, giving actual finite
level in the original definition.

The internal construction first chooses finitely many actual point
evaluations separating the finite-dimensional orbit span. It uses a
minimal intersection of evaluation kernels, available by the Artinian
condition on a finite-dimensional complex space. The same general
finite-separation method appears for endomorphism spaces in the
published `exists_finset_eq_zero_of_apply_eq_zero`; the present proof
works directly on the original adelic functions.

Each of those orbit evaluations is locally constant by the original
finite-slice condition and continuity of finite multiplication. Their
finite intersection forces equality of whole functions, proving local
constancy of the function-valued orbit. Its identity fiber is the actual
stabilizer and is open. Mapping it through the actual open-subgroup
inclusion gives an open subgroup of the full finite adelic group. That
subgroup is closed and contained in the specified compact subgroup,
which proves compactness.

This is a finite-level construction for the existing function carrier.
It does not infer algebraic-tensor rank from local constancy or
finiteness, and does not identify the broader smooth carrier with
GH (6.1). No representation-theoretic semisimplicity or automatic
archimedean growth assertion is used.
