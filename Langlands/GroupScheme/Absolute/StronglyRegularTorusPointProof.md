# Strongly regular points of a maximal torus

Author: Worker 1729.

`Langlands.GroupScheme.algClosedStronglyRegularTorusPoint.{u}` proves exactly
`Langlands.GroupScheme.AlgClosedStronglyRegularTorusPointStatement.{u}` from
`Absolute/StronglyRegularTorusPointStatement`, with one arbitrary universe
parameter and no additional premises. For a maximal torus `j : T ⟶ G` of a
connected reductive group over an algebraically closed field, it constructs a
nonempty open subset of `T` such that the centralizer of each rational point
in that subset is contained in `T` on every test scheme. The tests may be
nonreduced or nonaffine.

## Implemented proof

Choose a closed linear embedding `ρ : G ⟶ GLₙ` using
`affineLinearEmbeddingStatement`. The torus is split by the published
`torusFiniteGaloisSplitting` and
`IsTorus.isSplitTorus_of_finiteGaloisSplitting`.

`StronglyRegularTorusPoint.exists_rationalDiagonal` applies
`SplitTorusGenericWeights.exists_splitTorusDiagonal` to `ρ` restricted to
`T`. If `P` is its change of basis, conjugate the actual representation by
the rational general linear point corresponding to `P⁻¹`. This gives a
representation `σ` which remains monomorphic and whose rational torus
matrices are diagonal. This helper needs only a split torus over a field.

The torus is integral by `IsTorus.isIntegral` and smooth by
`IsTorus.smooth`, hence reduced and locally of finite type.
`StronglyRegularTorusPoint.universal_diagonal` uses `eq_of_rationalEval`
to show that every off-diagonal entry of the universal matrix of
`σ` restricted to `T` vanishes. Write its diagonal entries as
`dᵢ ∈ Γ(T, O)`. The helper
`StronglyRegularTorusPoint.point_diagonal` pulls this identity back along
an arbitrary point `y : Z ⟶ T`: its matrix is diagonal with entries
`y*(dᵢ)`.

`StronglyRegularTorusPoint.exists_separatingOpen` forms the product

```text
F = ∏ (i,j), if dᵢ = dⱼ then 1 else dᵢ - dⱼ.
```

The ring of global sections of an integral scheme is a domain, so `F ≠ 0`.
The basic open `D(F)` is nonempty because on a reduced scheme a basic open
is empty exactly when its defining global section is zero. If a rational
point `t` has image in `D(F)`, then `t*(dᵢ - dⱼ)` is nonzero in the base
field whenever `dᵢ ≠ dⱼ`. The proof pulls back the basic open to `Spec k`:
a zero evaluation would make that pullback empty, contradicting membership
of the closed point of `Spec k`.

`StronglyRegularTorusPoint.commute_diagonal_of_units` is an elementary
matrix lemma over any commutative ring. Suppose a matrix `M` commutes with
`diag(a)`. Its `(i,j)` equation gives `(aᵢ - aⱼ) Mᵢⱼ = 0`.
Consequently it commutes with `diag(b)` whenever, for each pair of indices,
either `bᵢ = bⱼ` or `aᵢ - aⱼ` is a unit.

`StronglyRegularTorusPoint.mem_centralizer_of_separating` applies this lemma
on every refinement `V ⟶ Z` and against every `V`-point `y` of `T`.
Commutation of `c : Z ⟶ G` with `t` pulls back to `V`. In the matrices of
`σ`, take `aᵢ` to be the scalar image of `t*(dᵢ)` and `bᵢ = y*(dᵢ)`.
If `dᵢ = dⱼ`, then `bᵢ = bⱼ`; otherwise `aᵢ - aⱼ` is a unit because
it is the image of a nonzero field element. Injectivity of `σ.pointMatrix`
therefore proves that `c` belongs to the all-test torus centralizer.
No reducedness, affineness or nonemptiness is assumed of these tests.

Finally, `algClosedMaximalTorusCentralizer_fromQuotient`, supplied with
the proved `dynamicCentralizerReductive` and `solvableTorusQuotient`,
identifies the torus centralizer with `SubgroupFunctor.range j`.
Membership in that range is precisely the required factorization of `c`
through `T`.

## Provenance and relation to the source statement

This is a derived representation proof assembled from the imported Library
results and the elementary matrix argument above. The helpers in this
module are internal consequences used for that proof. Their provenance is
the displayed constructions and arguments, not additional assertions from
the original literature.

The statement's Markdown explains Steinberg's classical strongly regular
locus through root values and Weyl fixed points, and a scheme-theoretic
upgrade using smooth fixed-point schemes. This proof instead separates the
finitely many weights occurring in a faithful representation. It constructs
a sufficient nonempty open subset; it does not identify the entire strongly
regular locus or its root/Weyl characterization. The matrix argument works
directly on all tests, so it does not require a smoothness theorem for the
centralizer of a group point. The source interpretation and scope remain
those of `Absolute/StronglyRegularTorusPointStatement.md`.
