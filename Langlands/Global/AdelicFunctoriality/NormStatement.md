# Local/global compatibility for actual adelic norms

`NormCompatibility` is an exact proposition definition, not a theorem. It
conjoins two arithmetic obligations for arbitrary number fields `K : Type u`
and `L : Type v`, with their field, number-field and `Algebra K L` instances.
The universes are independent. Finite dimensionality follows from the
number-field hypotheses; it is not an added assumption.

`CompletedTensorComparison` asserts that the maps already constructed in
`Norm.lean` are bijective. At a finite place `p`, the map is

    K_p ⊗[K] L → ∏ (q above p), L_q,
    x ⊗ y ↦ (completionMap(p,q)(x) · y)_q.

The index is the actual subtype of height-one primes of the ring of integers
of `L` satisfying the lies-over relation. At an infinite place it is the
actual subtype of Mathlib infinite places above that place, with Mathlib's
completion embedding. The maps, scalar towers and tensor formulas are
constructed; the statement does not quantify over a proposed equivalence,
assume a decomposition theorem, or assume the desired norm identity.

`PrincipalNormCompatibility` asserts equality in the actual full adele ring
of `K`, for every `x : L`, including zero. Its left side applies the
constructed adelic norm to the diagonal adele of `x`. Its right side is the
diagonal image of `Algebra.norm K x`. Thus the statement fixes the precise
normalization and direction of the arithmetic norm. It is not an equality
only of absolute values or valuations, and it is not an extension-of-scalars
embedding. The already implemented norm is multiplicative and continuous;
this statement supplies the additional local/global arithmetic identity.

The tensor-decomposition obligation and the norm identity are separate
conjuncts so that their proof dependencies are visible. A proof may derive
the latter from the former using determinant compatibility with base change
and finite products. `Norm.lean` already proves the infinite-place comparison
from weak approximation and Mathlib's infinite local-degree sum. The
finite-place comparison and the global norm identity remain unproved;
the determinant argument is a proposed proof route, not claimed existing
Mathlib support or a completed proof. Passing from this identity to norms
on principal units and then the principal-idele quotient remains a further
construction obligation. No quotient norm is asserted to exist by this file.

The original source is Andre Weil, *Basic Number Theory*, second edition
(1973), Chapter III section 4, Theorem 4, printed pp. 56-57 (PDF pp. 73-74),
and Corollary 3, printed p. 58 (PDF p. 75). The adelic product formula is
Chapter IV section 1, Corollary 3, printed p. 64 (PDF p. 81). The determinant
definition of the norm and its behavior under algebra isomorphism and
products are in Chapter III section 3, printed pp. 53-54 (PDF pp. 70-71).
Registered original: `weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
These original pages were read. The precise displayed formulas are their
realization on the pinned Mathlib completions and the constructed adelic map.
