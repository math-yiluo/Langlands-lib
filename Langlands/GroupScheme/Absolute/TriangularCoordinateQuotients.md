# Actual quotient comparisons for the triangular coordinate series

This is an internal construction on actual group schemes over an arbitrary
field `k : Type u`. The two given quotients need not be smooth, connected or
reduced. Existence of quotients is an explicit premise only in the final
`seriesQuotient` construction; this module does not prove that premise or the
triangular diagonal splitting statement.

`TriangularLayer.QuotientTerm F` consists of an affine group scheme of locally
finite type, a homomorphism from `H`, and the assertion that this homomorphism
is an fppf quotient whose full kernel functor is exactly `F`. Here fppf means
flat, surjective on the underlying scheme and locally of finite presentation.
It does not assert surjectivity on the point group of every test scheme.
The structure's geometric fields supply instances. When `H` is affine, its
quotient morphism is also quasi-compact, since both schemes are affine.

Let `A` be such a quotient by `F`, let `B` be one by `E`, and assume `E ≤ F`.
The quotient by `F` kills the full kernel of the quotient by `E`.
`QuotientTerm.comparison A B hEF` is the actual homomorphism from `B.quotient`
to `A.quotient` obtained by fpqc homomorphism descent. Its factorization law is
`B.hom ≫ comparison = A.hom`. The full inverse image under `B.hom` of the
comparison's actual kernel equals `F` on every relative test scheme. The proof
uses the full kernel criterion and the factorization law in both directions.

The comparison is flat and surjective. For flatness, lift any point of
`B.quotient` along the underlying surjective morphism `B.hom`; the flat local
ring map of `A.hom` descends to the stalk map of the comparison through the
flat local ring map of `B.hom`, using `DominantHomFlat.flat_stalkMap_of_comm`.
This is descent for scheme stalks and requires no global lifts of test-scheme
points. Surjectivity follows from surjectivity of the composite `A.hom`.
The comparison is locally of finite type because `B.quotient` is locally of
finite type over `k`; its target is locally noetherian, being locally of finite
type over a field, so it is locally of finite presentation.
`comparison_isFppfQuotient` packages these results as an fppf quotient by the
comparison's full actual kernel.

Suppose further that `i : K ⟶ H` represents `F` as a subgroup functor.
`kernelRestriction A B hEF hi` is the restriction of `B.hom` from `K` to the
full scheme kernel of the comparison. It is constructed by the published
all-test Yoneda restriction, using the inverse-image equality just proved.
Its composite with the kernel inclusion is `i ≫ B.hom`.
`kernelRestriction_isPullback` proves that this square is cartesian in schemes
over the field. Base change therefore makes this restriction flat, surjective
and locally of finite presentation. Its full kernel functor is precisely
`E.comap i`: composing with the monic comparison-kernel inclusion detects the
identity, and the original quotient by `E` supplies its full kernel criterion.
`kernelRestriction_isFppfQuotient` records the resulting exact fppf quotient.

Finally, `seriesQuotient hquot j t` applies the explicitly supplied proposition
`AffineNormalSubgroupQuotientStatement` to the closed, normal actual subgroup
`seriesHom` from `TriangularCoordinateSeries`. It chooses an actual
`QuotientTerm` for every natural index `t`, assuming `H` is affine and locally
of finite type and `j` maps to the triangular block parabolic with the original
decreasing weights. This includes every matrix size, including zero. No
faithfulness, positivity or algebraic-closure hypothesis is used for this
choice. The module does not yet assemble the finite tower, identify its
successive kernels with closed additive images, descend character actions,
or construct a section.

The provenance is internal: the proofs specialize the published fpqc
homomorphism descent, represented-subgroup restriction and pullback interfaces,
and the general flat-stalk descent lemma. The only quotient-existence input
remains a displayed proposition argument. No external splitting theorem or
geometry of a reduced or connected diagonal kernel is invoked.
