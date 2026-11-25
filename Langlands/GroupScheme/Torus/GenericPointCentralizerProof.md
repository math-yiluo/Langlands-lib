# Proof: a torus has a point with the same centralizer (Milne 16.42)

`Langlands.GroupScheme.torusGenericPointCentralizer.{u}` proves exactly
`Langlands.GroupScheme.TorusGenericPointCentralizerStatement.{u}`, published in
[`Torus.GenericPointCentralizerStatement`](GenericPointCentralizerStatement.md).
The theorem adds no hypotheses. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

The setting is that of the statement. `k` is an algebraically closed field and
`S = Spec (CommRingCat.of k)`. `G : GroupScheme S` satisfies `[Smooth G.X.hom]`,
`[IsAffineHom G.X.hom]` and `[ConnectedSpace G.X.left]`. `T : CommGroupScheme S` comes
with `j : T.toGrp ⟶ G`, `IsClosedSubgroup j` and `IsTorus T.toGrp`. The proof gives a
rational point `s : 𝟙_ (Over S) ⟶ T.X` with

```text
G.pointCentralizer (s ≫ j.hom.hom) = torusCentralizer j
```

as subgroup functors of `G`, that is, on every test scheme over `S`.

Three hypotheses are not used: `IsClosedSubgroup j`, `ConnectedSpace G.X.left`, and
smoothness of `G` beyond the fact that it makes `G` locally of finite type. The argument
works for any homomorphism from a torus into an affine group of finite type over `k`.

## Declarations in this module

- `TorusGenericPointCentralizer.torusCentralizer_le_pointCentralizer`: for every field
  `k`, every homomorphism `j : T.toGrp ⟶ G` and every rational point `s` of `T`,
  `torusCentralizer j ≤ G.pointCentralizer (s ≫ j.hom.hom)`.
- `torusGenericPointCentralizer`: the target theorem.

## The proof

**The easy inclusion.** Take a point `c : Z ⟶ G.X` of `torusCentralizer j` over a test
scheme `Z`. The definition of `torusCentralizer`
(in [`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md)) applies to the
identity of `Z` and the torus point `toUnit Z ≫ s`. It says that `c` commutes with
`(toUnit Z ≫ s) ≫ j.hom.hom`, which is the pullback of `s ≫ j.hom.hom` to `Z`. By
`mem_pointCentralizer` (in [`PointCentralizer`](../PointCentralizer.md)) this means that
`c` lies in `G.pointCentralizer (s ≫ j.hom.hom)`. This is
`torusCentralizer_le_pointCentralizer`, and it holds for every rational point `s`.

**Choosing the point.** The rest of the proof takes the steps of the published proof
`algClosedStronglyRegularTorusPoint`
(in [`Absolute.StronglyRegularTorusPointProof`](../Absolute/StronglyRegularTorusPointProof.md))
and uses its lemmas in the namespace `StronglyRegularTorusPoint`. It omits the final
step, which needs reductivity and a maximal torus.

1. *Geometry of `T`.* `IsTorus.smooth` (in [`Torus.Geometry`](Geometry.md)) and
   `IsTorus.isIntegral` (in [`Torus.Integral`](Integral.md)) show that `T → S` is smooth
   and that `T` is integral. In particular `T` is reduced and locally of finite type.
2. *A faithful representation.* `G` is affine, and it is locally of finite type because it
   is smooth. The published theorem `affineLinearEmbeddingStatement`
   (in [`AffineLinearEmbeddingProof`](../AffineLinearEmbeddingProof.md)) therefore gives
   `N` and `ρ : MatrixRepresentation G (Fin N)` with `IsClosedSubgroup ρ`. So the
   underlying morphism of `ρ` is a closed immersion, and hence a monomorphism.
3. *`T` is split.* The field `k` is algebraically closed. So
   `IsTorus.isSplitTorus_of_finiteGaloisSplitting` (in
   [`Torus.SplitReflection`](SplitReflection.md)), applied to the published proof
   `torusFiniteGaloisSplitting` (in
   [`Torus.FiniteGaloisSplittingProof`](FiniteGaloisSplittingProof.md)), gives
   `IsSplitTorus T.toGrp`.
4. *Diagonalization.* `StronglyRegularTorusPoint.exists_rationalDiagonal` conjugates `ρ`
   by a rational invertible matrix. The result is a representation `σ` whose underlying
   morphism is again a monomorphism, and the matrix of `σ.restrict j` is diagonal at every
   rational point of `T`.
5. *Universal diagonal.* Let `d i ∈ Γ(T.X.left, ⊤)` be the diagonal entries of the
   universal matrix `(σ.restrict j).pointMatrix T.X (𝟙 T.X)`. `T` is reduced and locally of
   finite type over the algebraically closed field `k`, so a function on `T` is determined
   by its values at rational points. `StronglyRegularTorusPoint.universal_diagonal` uses this
   to show that the universal matrix equals `diagonal d`. Thus every point `y` of `T` over
   any test scheme acts through `σ` by the diagonal matrix with entries the pullbacks of
   `d i` along `y`.
6. *A separating open.* `T` is integral. For `StronglyRegularTorusPoint.exists_separatingOpen d`,
   let `F` be the product of the differences `d i - d j` over the pairs with `d i ≠ d j`.
   Then `F ≠ 0`, the basic open `U` of `F` is nonempty, and at every rational point `t`
   whose image lies in `U`, `d i - d j` has nonzero value whenever `d i ≠ d j`.
7. *A rational point in `U`.* `T` is locally of finite type over the algebraically closed
   field `k`. The published `ClosedRationalPoints.exists_rationalPoint_mem` (in
   [`AlgebraicGeometry.ClosedRationalPoints`](../../AlgebraicGeometry/ClosedRationalPoints.md))
   gives a rational point `s` of `T` whose closed point maps into `U`. The space of
   `Spec k` has only one point, so the whole image of `s` lies in `U`. This `s` is the
   required point.

**The hard inclusion.** Let `c : Z ⟶ G.X` be a point of `G.pointCentralizer (s ≫ j.hom.hom)`.
By `mem_pointCentralizer`, `c` commutes with `toUnit Z ≫ s ≫ j.hom.hom`.
`StronglyRegularTorusPoint.mem_centralizer_of_separating` then shows that `c` lies in
`torusCentralizer j`. That lemma argues with matrices on every test scheme as follows.

- Take a test scheme `V`, a morphism `a : V ⟶ Z` and a torus point `y : V ⟶ T.X`.
- Through `σ`, the pullback of `s` to `V` acts by the constant diagonal matrix with entries
  `λ_i`, the images in `Γ(V, ⊤)` of the values `d i (s) ∈ k`. The matrix `M` of `a ≫ c`
  commutes with it.
- If `d i ≠ d j`, then `λ_i - λ_j` is the image of a nonzero element of `k`, hence a unit,
  and `(λ_i - λ_j) M_ij = 0` forces `M_ij = 0`. If `d i = d j`, the pullbacks of `d i` and
  `d j` along `y` are equal (`commute_diagonal_of_units`).
- So `M` commutes with the diagonal matrix of `y` from step 5. Points of `G` are detected
  through the monomorphism `σ` (`pointMatrix_injective`), so `a ≫ c` commutes with
  `y ≫ j.hom.hom`. This is membership in `torusCentralizer j`.

The two inclusions give equality by `le_antisymm`.

## Comparison with the source

J. S. Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`, Lemma 16.42,
p.339. Milne also decomposes a faithful representation into eigenspaces of the torus (12.12)
and chooses `s` outside the proper closed subsets `χ_i(s) = χ_j(s)`, `i ≠ j`. He then shows
`C_G(s)(k) ⊂ C_G(S)(k)` on rational points and uses smoothness of `C_G(s)` (13.8) to conclude
equality of algebraic subgroups. The Lean proof does not use smoothness of the centralizer.
It proves the inclusion of subgroup functors directly on every test scheme: differences of
distinct eigenvalues of `s` are nonzero elements of `k`, so they remain units in every
`k`-algebra. This is why connectedness and smoothness of `G` are not needed beyond finite
type.
