# Affine evaluation and matrices of the Harris cocharacters

This module constructs evaluation of the existing complex Harris group cocharacters on units of an arbitrary commutative complex algebra. It proves the resulting diagonal matrices over that algebra. The content is an internal specialization of the published group-scheme and matrix constructions, not a new interpretation of an external theorem.

## Relative affine unit points

For commutative rings R and T in the same universe with an R-algebra structure on T, `GroupScheme.Gm.relativeAffineUnitPoint R T u` is the point of the multiplicative group over Spec R associated to u in Tˣ. Its source is the actual relative affine test object `(algSpec R).obj (op T)`. It is constructed by the inverse of `Gm.affinePointsEquiv` for the structure morphism Spec T → Spec R.

`relativeAffineUnitPoint_sections` says that applying `Gm.pointsEquiv` and then the canonical relative section algebra equivalence Γ(Spec T) → T gives the underlying element of u. The proof uses the inverse law of the affine point equivalence and `Corepresented.affineSectionsIso_hom_ringHom`, which identifies the normalization with the usual spectrum/global-sections isomorphism.

## Coefficient change for diagonal matrices

`ComplexMatrix.splitDiagonal_map` applies to commutative rings S and T, a ring homomorphism f : S → T, natural numbers n and r, and p in S × S. Applying f entrywise to both matrices of `splitDiagonal S n r p` gives `splitDiagonal T n r (f p.1, f p.2)`. The proof compares entries and splits the diagonal and block-index conditions. No bound on r is needed.

## Evaluation in the Harris group

Let D be the existing `CentralSimpleUnitaryData E K A n`: E is a totally real number field, K is a totally complex quadratic extension of E, and A carries the specified compatible E-, K- and rational algebra structures. Let C be `HarrisSignatureCharts D.toSecondKindInvolution n Φ`, with its distinguished real embedding. The inherited hypotheses include the scalar towers ℚ → E → A, ℚ → K → A and E → K → A.

For a universe-zero commutative complex algebra T, `D.complexAffineCocharacterValue T χ u` evaluates a group-scheme morphism χ : Gm over ℂ → D.complexRationalGroupScheme by composing the relative affine unit point with χ. This definition does not require signature charts or a separately supplied real-algebra structure on T.

The theorem `harrisCocharacter_affine_matrices` additionally assumes the real algebra structure on T and its tower ℝ → ℂ → T. For every Boolean `first`, unit u in Tˣ and real embedding τ, the matrices of the actual evaluated cocharacter are

```
splitDiagonal T n r (u, 1)     if first = true,
splitDiagonal T n r (1, u)     if first = false,
```

where r = n − 1 at `C.distinguished` and r = n otherwise, and u denotes its underlying element. For a pair (z,w), the first matrix has diagonal w for i < r and z otherwise; the second has diagonal z for i < r and w otherwise. All off-diagonal entries vanish. Thus this retains the ordering and corrected weights of `ComplexMatrix.splitDiagonal`.

The implemented proof first uses `complexAffinePointMatrices_sections` to express affine coordinates as normalized global-section matrices, then applies `harrisCocharacter_matrices` on the actual affine test scheme. `splitDiagonal_map`, the relative unit normalization and preservation of 1 by the section ring map finish the calculation.

## Provenance and scope

The constructions use the existing Laurent-polynomial multiplicative group (`GroupScheme.Multiplicative`), the relative affine section comparison (`GroupScheme.CorepresentedAffineComparison`), and the actual Harris group and cocharacter matrices from `ComplexAffineMatrices` and `ComplexCocharacterMatrices`. These dependencies supply the original Harris conventions; this module only derives their affine evaluation formulas.

The result holds for every specified test algebra, not just complex-valued points. Identification with the separate identity-test evaluation, embedding-labelled cocharacter formulas, reflex conjugacy, smoothness and reductivity, and construction of Shimura scheme levels remain separate obligations. No such assertion is assumed or claimed here.
