# Proof: quasi-split inner forms over Picard-trivial bases, `Spec ℤ` and affine spaces

This module proves the published proposition
[`ReductivePicardTrivialQuasiSplitInnerFormStatement`](PicardTrivialQuasiSplitInnerFormStatement.md)
(Conrad, *Reductive group schemes* (2014), Remark 7.2.13) in every universe `u`. The
theorem is

```lean
theorem Langlands.GroupScheme.reductivePicardTrivialQuasiSplitInnerFormStatement :
    ReductivePicardTrivialQuasiSplitInnerFormStatement.{u}
```

The module adds this one theorem. Its proof is a single term: it applies the published
assembly theorem
`reductivePicardTrivialQuasiSplitInnerFormStatement_of_prerequisites` (module
[`PicardTrivialInnerFormAssembly`](PicardTrivialInnerFormAssembly.md)) to six published
Library results, all instantiated in universe `u`. The assembly derives the three clauses
of the target from these six inputs. The Markdown of that module describes the derivation.

## The six inputs

1. `hModel`: the published theorem `relativeQuasiSplitInnerFormExistence`
   (module `Langlands.GroupScheme.Reductive.RelativeQuasiSplitInnerFormProof`), which proves
   `RelativeQuasiSplitInnerFormExistenceStatement`.
2. `hQuot`: the published theorem `relativeAdjointQuotientExistence`
   (module `Langlands.GroupScheme.Adjoint.RelativeExistenceProof`), which proves
   `RelativeAdjointQuotientExistenceStatement`.
3. `hFil`: the published theorem `relativeUnipotentRadicalFiltration`
   (module `Langlands.GroupScheme.RelativeUnipotent.RadicalFiltrationProof`), which proves
   `RelativeUnipotentRadicalFiltrationStatement`.
4. `hWeil`: the published theorem `relativeBorelAdjointTorusWeilPresentation`
   (module `Langlands.GroupScheme.RelativeLevi.AdjointTorusWeilPresentationProof`), which
   proves `RelativeBorelAdjointTorusWeilPresentationStatement`.
5. `hZ` asks: for every `R : Type u` with `Nonempty (R ≃+* ℤ)`, every module-finite étale
   `R`-algebra `R' : Type u` has `Subsingleton (CommRing.Pic R')`. The proof supplies
   `fun R _ h => Langlands.Algebra.finiteEtaleAlgebrasHaveTrivialPicard_of_ringEquiv_int.{u, u} R h`.
   That theorem (module `Langlands.Algebra.IntegerFiniteEtalePicard`) returns
   `FiniteEtaleAlgebrasHaveTrivialPicard.{u, u} R`. This proposition unfolds to exactly the
   required statement about every `R' : Type u`.
6. `hAff` asks for the body of `Langlands.Algebra.AffineSpaceFiniteEtalePicardTrivialStatement.{u}`:
   for a field `k` of characteristic zero, every module-finite étale `k[x₁, …, xₙ]`-algebra
   `A` has trivial Picard group. The proof supplies
   `Langlands.Algebra.affineSpaceFiniteEtalePicardTrivial_of_polynomialProduct
   Langlands.Algebra.affineSpaceFiniteEtalePolynomialProduct.{u}`. Here
   `affineSpaceFiniteEtalePolynomialProduct` (module
   `Langlands.Algebra.AffineSpaceFiniteEtalePolynomialProductProof`) proves
   `AffineSpaceFiniteEtalePolynomialProductStatement`: such an `A` is ring-isomorphic to a
   finite product of polynomial rings `K_i[x₁, …, xₙ]` over fields. The reduction
   `affineSpaceFiniteEtalePicardTrivial_of_polynomialProduct` (module
   `Langlands.Algebra.AffineSpaceFiniteEtalePicardReduction`) turns this into the Picard
   statement.

## Imports and axioms

The module imports the assembly module and the seven modules that contain the inputs
above. No other declarations are added. The theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.
