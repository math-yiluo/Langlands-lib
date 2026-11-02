# Levi decomposition of the quasi-split unitary dynamic parabolic: statement

`Langlands.GroupScheme.QuasiSplitUnitary.LeviDecompositionStatement` is a
proposition definition for a separate proof unit. Its hypotheses are fields
`F` and `E`, an `F`-algebra structure and `IsQuadraticExtension F E`, a finite
`F`-basis `b` of `Matrix (Fin 2) (Fin 2) E`, and a nonidentity automorphism
`c : E ≃ₐ[F] E`. There is no characteristic restriction.

For `G = groupScheme b c`, write `λ = cocharacter b c` and
`λ' = inverseCocharacter b c`. The proposition is the conjunction of four
assertions:

1. `Dynamic.unipotent λ` is normalized by `Dynamic.parabolic λ`, in the
   precise sense of `SubgroupFunctor.IsNormalizedBy`: conjugation by every
   parabolic point over every test scheme preserves the unipotent subgroup.
2. For every test scheme `T` over `Spec F` and every point `g` in
   `(Dynamic.parabolic λ).carrier T`, there is a unique ordered pair of points
   `(z,v)` with `z` in `(Dynamic.centralizer λ).carrier T`, `v` in
   `(Dynamic.unipotent λ).carrier T`, and `g = z * v`.
   Uniqueness applies to the pair including both membership requirements.
3. The intersection `Dynamic.parabolic λ ⊓ Dynamic.parabolic λ'` equals
   `Dynamic.centralizer λ` as a subgroup functor.
4. The intersection `Dynamic.unipotent λ' ⊓ Dynamic.parabolic λ` is the bottom
   subgroup functor, whose points consist only of the identity.

These claims hold on all test schemes, including non-reduced schemes, because
the first two explicitly quantify over them and the last two are equalities of
subgroup functors. The ordering in the factorization is centralizer first and
unipotent second.

Milne, *Algebraic Groups* (2017), Theorem 13.33 and its proof, printed
pp.265–266, supply the general dynamic decomposition framework and the
opposite-unipotent intersection used there. Example 13.31, printed pp.264–265,
computes the analogous matrix subgroups for `SL₂`. The full-unitary statement
here is derived by applying the dynamic framework to the antidiagonal
hermitian presentation; it is not attributed to the `SL₂` example as a unitary
theorem. For the underlying unitary algebra-involution framework see Milne,
Proposition 24.40, Definition 24.42 and Theorem 24.44, printed pp.523–525;
the last theorem concerns special unitary groups, whereas `G` uses the
Library's full unitary model. This module defines the target proposition and
provides no proof.
