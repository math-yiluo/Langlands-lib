# Scalar extension of the actual adjoint differential

This is an internal derived comparison between the actual adjoint representation
of an affine group scheme, its coefficient extension, and its scheme pullback.
The main consequence is a polynomial nonnilpotence criterion over the original
field. The derivation uses the constructed Lie kernels, their published scalar
extension and scheme pullback equivalences, natural finite coordinates, and the
linear-algebraic polynomial detection of nonnilpotence. No external group
structure theorem is used in this module.

Let `k` and `K` be fields in an arbitrary common universe, with a `k`-algebra
structure on `K`. Write `G_K` for the actual scheme pullback of `G` along
`Spec K → Spec k`. Except where explicitly weakened below, assume that `G` is
affine and locally of finite type over `k`, and let `c : FiniteCoordinates G d`
be natural coordinates for its actual Lie kernels on all coefficient algebras.
No perfectness, characteristic, smoothness, connectedness, splitting, or
positive-dimension hypothesis is imposed.

`coordinateTensorEquiv d` is the standard basis equivalence
`K ⊗[k] (Fin d → k) ≃ₗ[K] (Fin d → K)`. On a pure tensor `a ⊗ v` it has
coordinates `a * algebraMap k K (v i)`. The lemma
`coordinateTensorEquiv_baseChange` shows that it intertwines the scalar extension
of a matrix endomorphism with its entrywise coefficient extension. The proof is
tensor induction and the finite matrix multiplication formula.

`adjointDifferentialFamily_scalarExtension` compares simultaneous extension of
the parameters and the endomorphisms of `adjointDifferentialFamily c` with the
actual tangent matrix at `kernelScalarExtension G K z`. Tensor induction on `z`
reduces the comparison to epsilon scaling and coefficient naturality of actual
tangent matrices. Addition of parameters is the raw dual-number kernel product,
whose tangent matrix is the sum. The lemma
`coordinateTensorEquiv_conj_adjointDifferentialFamily` expresses this comparison
as conjugation by the coordinate equivalence, so it preserves nilpotence.

`adjointRepresentation_baseChange_affineAction` proves equality of the two
adjoint actions in the pulled-back coordinates on every commutative test
`K`-algebra `A`, including any given compatible `k`-algebra structure on `A`.
The proof identifies that structure with the composite algebra structure, uses
surjectivity of the coordinates, and applies the actual adjoint equivariance of
`kernelBaseChangeLinearEquiv`. It requires only affineness of `G`.
`adjointRepresentation_baseChange_tangentMatrix`, also requiring only
affineness, applies the action comparison on dual numbers. Equality of matrix
actions gives equality of matrices; extracting their epsilon coefficients gives
the tangent matrix equality under `kernelBaseChangeEquiv`.

`not_isNilpotent_adjointFamilyBaseChange` transports any nonnilpotent adjoint
differential at an actual `K`-Lie element of `G_K` to a nonnilpotent member of
the scalar-extended ground-field family. The proof maps a putative nilpotence
through conjugation and then uses the tangent matrix comparison.
`exists_nonnilpotent_adjointFamilyBaseChange` obtains such a member from the
explicit hypothesis that there exists `X : lieKernel G_K K` which is
`IsSemisimpleElement G_K X` and has `elementCentralizerLie G_K X ≠ ⊤`.
Here semisimplicity is the existing representation-semisimplicity predicate, and
properness refers to the tangent centralizer submodule. The input theorem from
`AdjointDifferentialCentralizer` proves that this actual adjoint differential
is nonnilpotent.

`exists_polynomial_nonnilpotent_adjoint_locus`, for any basis indexed by
`Fin d` of the ground-field Lie module, gives a nonzero polynomial whose
nonvanishing implies that the actual ground-field adjoint differential is
nonnilpotent. It applies `exists_polynomial_nonnilpotent_locus` to the preceding
geometric member; the polynomial comes from a characteristic-polynomial
coefficient below the leading term.

Finally, `nonnilpotent_adjoint_locus_spans_of_geometric_semisimple` assumes
additionally that `k` is infinite. Under the same explicit geometric existence
hypothesis it proves both existence of a ground-field Lie element with
nonnilpotent adjoint differential and that all such elements span the entire
ground-field Lie module. Its basis is supplied by `c`, and the proof applies
`nonnilpotent_locus_spans_of_baseChange`.

The geometric existence premise is retained. The module does not prove that a
nonnilpotent Lie element can be replaced by a noncentral semisimple element
which it centralizes, nor does it prove spanning by semisimple centralizers or
Cartan generation. Those require additional Lie-theoretic and group-structural
arguments, including the imperfect-field and bad-characteristic cases.

The local instances have explicit module-specific names to avoid generated-name
collisions when these developments are imported together. Their types, bodies
and local scope are unchanged.
