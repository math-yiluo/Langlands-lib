# Root-coordinate matrices on the normalized path basis

This is an internal linear algebra prerequisite for the even-path cross-section calculation. It derives exact root-coordinate and ordinary simple-factor matrices from the published affine polynomial action and normalized path vectors.

For an arbitrary field `k : Type u`, an actual affine group scheme with supplied split pinning, and a finite decidable representation index `d : Type`, `RootParametrization.affinePoint_eq_constantPoint_rationalPoint` identifies extension of a rational root coordinate `c` with the affine root point of coordinate `algebraMap k A c` over each commutative `k`-algebra `A`. Its proof uses naturality of the spectrum/global-sections isomorphism and the published naturality of root points. Consequently, when all divided powers of degree at least two vanish, `RootParametrization.rationalMatrix_eq_one_add` gives the actual matrix `1 + c • coefficientMatrix 1` with this exact scalar `c`.

Now supply a highest-weight representation at a weight fundamental at the first vertex of a type-A path component, a normalized simple-root family `x`, and a nonzero initial vector in the first path weight space. Use the normalized basis constructed in `PathNormalizedMatrices`. For a vertex `i : Fin L`, `pathRootMatrix i c` is `1 + Matrix.single i.castSucc i.succ c`: it adds `c` times vector `i` to vector `i+1` and fixes all other normalized path vectors.

The two vector-action theorems prove these claims for the actual point `(x (β i)).toRootParametrization.rationalPoint c`. The higher divided powers vanish by the published path-root calculation. The first divided power takes vector `i+1` to vector `i` by the normalization and kills every other path vector. Taking coordinates in the normalized basis yields the two column theorems and the complete equality `normalizedPathMatrix_rationalRoot`.

`pathSimpleFactorMatrix i c` is `pathReflectionMatrix i - Matrix.single i.castSucc i.castSucc c`. Direct matrix multiplication proves that it equals `pathRootMatrix i c * pathReflectionMatrix i`; its consecutive block is

```
[-c  1]
[-1  0].
```

The monoid-homomorphism property of `normalizedPathMatrix`, together with the root and canonical reflection formulas, then proves `normalizedPathMatrix_simpleFactor`: this is the actual matrix of `x_(β i)(c) n_(β i)`. All formulas hold in arbitrary characteristic, with no algebraic-closure or path-parity assumption.

This module does not calculate merged-root factors or modified-product characteristic polynomials and does not assert the canonical class-quotient cross-section theorem.
