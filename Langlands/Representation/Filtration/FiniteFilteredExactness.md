# Finite filtered exactness

Author: Worker 194.

This internal algebraic prerequisite proves that exactness and injectivity of
actual associated graded maps lift through a finite filtration. It works over
any commutative ring `R`, with independent universes for the ring and the three
modules. It assumes no finite dimension, splitting, topology, smoothness,
finite length or representation classification.

For a family of submodules `S`, `denominator S i` is the inverse image of
`S i` under the inclusion of `S (i+1)`. The module `Graded S i` is the actual
quotient of `S (i+1)` by that submodule. When the family is increasing, this is
the usual adjacent quotient. The definitions also make sense without an
increasing-family assumption; no such assumption is silently built into a
generic quotient.

`Preserves f S T` means that the linear map `f` sends each `S i` into `T i`.
`stepMap` restricts `f` to the next steps, and `gradedMap` descends this
restriction to their actual quotients using `Submodule.mapQ`.
`gradedMap_mk` states that the induced map sends the class of a representative
to the class of its image. The maps are constructed, not supplied as
unspecified quotient data.

For two maps `f : A →ₗ[R] B` and `g : B →ₗ[R] C` preserving the three
families `S,T,U`, `reduction_of_graded_exact` uses equality of the graded
range and kernel in one grade. If `b ∈ T (i+1)` and `g b ∈ U i`, the class
of `b` is a graded cycle. Graded exactness gives a preimage in `Graded S i`;
surjectivity of the actual quotient map lifts it to `a ∈ S (i+1)`.
Equality of the quotient classes says precisely that `b - f a ∈ T i`.
The proof uses neither a section of the quotient nor a chosen splitting.

`lift_cycle_by_induction` performs this reduction finitely many times.
Its assumptions are that `S` is increasing, `T 0 = ⊥`, the actual
composite `g (f a)` vanishes for every `a`, and the induced quotient maps
are exact in all grades `i < n`. It proves that every actual cycle in
`T i`, for `i ≤ n`, is the image of a vector in `S i`.
At zero the cycle is zero. At a successor step the reduction above
subtracts one boundary, and the remainder is still a cycle because
`g ∘ f = 0`. The induction hypothesis lifts the remainder from the lower
step; monotonicity of `S` permits adding its lift to the first one.
`range_eq_ker_of_graded_exact` additionally assumes `T n = ⊤` and concludes
equality of the actual range of `f` and kernel of `g`.
No exhaustivity assumption on `S` or `U` is needed for this conclusion.

`lower_step_of_graded_injective` gives the corresponding one-step
injectivity argument. If `a ∈ S (i+1)` and `f a = 0`, injectivity of the
induced graded map implies that the class of `a` is zero, hence `a ∈ S i`.
`injective_of_graded_injective` repeats this descent, assuming
`S 0 = ⊥`, `S n = ⊤` and graded injectivity for every `i < n`.
It proves that the actual kernel of `f` is zero and then applies the result
to the difference of two vectors. This argument needs neither monotonicity
nor zero and full endpoints for the target family. The case `n=0` is included;
the simultaneous zero and full endpoint assumptions then force the relevant
module to be zero.

The provenance is internal. These are direct finite induction proofs using
actual quotient representatives, linearity and submodule membership.
The intended Aubert application must separately construct a finite
filtration preserved by its actual differentials, identify the induced
quotient maps, and establish their graded exactness or injectivity.
This module proves none of the Bruhat support, two-sided support-image,
orbital-integral, exterior-sign or graded-identification assertions.
It makes no assertion that a whole complex ending in zero is exact and
does not remove the surviving terminal homology.
