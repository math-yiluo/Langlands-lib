# Quasi-affine full-normalizer orbit targets for finite diagonalizable groups

For any commutative ring `R`, finite abelian character group `M`, and relatively
affine group scheme `G` locally of finite presentation over `Spec R`,
`normalizerOrbitModel R M G i hi` constructs an actual quasi-affine scheme `Y`
and a morphism from `G` to `Y` for every closed embedding `i : D_R(M) → G`.
For every relative scheme test `T` and points `g,h`, the orbit-map images agree
if and only if `g⁻¹ * h` lies in the full all-refinement normalizer of `i`.

There are no explicit locality or faithfulness premises. Finiteness of `M`
makes its character automorphism group finite. The action index is
`(Multiplicative (M ≃+ M))ᵐᵒᵖ`; an equivalence `g` is indexed by
`MulOpposite.op (Multiplicative.ofAdd g)`. This is the order required by
precomposition on embedding parameters.

The construction takes the full quasi-affine closed-embedding model and its
finite free character action. The effective finite free quasi-affine quotient
supplies its quotient scheme. `sourceCharacterIso_locallyExhaust` verifies
the local source-isomorphism premise using the arbitrary-test diagonalizable
automorphism locality theorem. The generic `NormalizerOrbit` construction
then supplies exactly the asserted all-test normalizer fibers and
quasi-affineness.

The result is derived from these imported constructions. The ambient group
need not be smooth. The homogeneous quotient by a smooth represented normalizer
is constructed in a subsequent step from this orbit target.
