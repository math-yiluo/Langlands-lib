# Reduction of local-to-global quadratic isometry to isotropy

Workers 787 and 864.

`Langlands.NumberFieldQuadraticIsometryReductionStatement.{u}` says that
`Langlands.NumberFieldQuadraticIsotropyStatement.{u}` implies
`Langlands.NumberFieldQuadraticIsometryStatement.{u}`.
`Langlands.numberFieldQuadraticIsometry_of_isotropy` proves this implication.
The isotropy theorem is its sole arithmetic premise.

## Proof

The proof works with finite-dimensional spaces of equal dimension over a
number field \(F\) and inducts on their dimension. At dimension zero both
spaces are subsingletons, so the unique linear equivalence is an isometry.

In positive dimension, nondegeneracy of \(q\) gives a vector \(x\) with
nonzero value \(a=q(x)\). An isometry over a completion \(A\) sends
\(1\otimes x\) to a vector \(y_A\) of value \(a\) in the scalar extension
of the second form \(r\). The vector \((1,y_A)\) is a nonzero zero of the
orthogonal sum of the line with coefficient \(-a\) and the extension of
\(r\). This sum is isometric to the tensor extension of the corresponding
global sum by tensor distribution over products and the tensor unit map.

The global sum is nondegenerate. Pairing with the scalar axis and the
second factor successively forces the two coordinates of a radical vector
to vanish. Applying the isotropy premise produces a nonzero zero
\((t,y)\) of that sum over \(F\). If \(t\) is nonzero, \(t^{-1}y\) has value
\(a\) under \(r\). If \(t=0\), then \(y\) is nonzero and isotropic for \(r\).
Choose \(z\) with \(\operatorname{polar}(r)(y,z)\ne 0\) by nondegeneracy.
The vector \(z+((a-r(z))/\operatorname{polar}(r)(y,z))y\) has value \(a\).

For each form, the line spanned by a vector of value \(a\) has orthogonal
complement given by the polar bilinear form. Their product is linearly
equivalent to the original space by `Submodule.prodEquivOfIsCompl`, and
the quadratic addition formula makes this an isometry. The restricted
form on the complement is nondegenerate, and its dimension is one less.

The isometries of these orthogonal decompositions extend to the actual
completion tensors. Preservation of the quadratic form follows by checking
the composed quadratic maps on \(1\otimes z\). The two decompositions then
have the same scalar line, so `quadraticForm_equivalent_of_prod_smul_sq`
cancels it and gives local isometries of the complements. The induction
hypothesis gives their global isometry. Taking its orthogonal product
with the identity of the line gives the original global isometry.

## Provenance

The reduction follows the common-value argument of John Voight,
*Quaternion Algebras*, Springer, 2021, Corollary 14.3.7 (printed p. 225) and
Corollary 26.8.25 (printed p. 451), with one-dimensional Witt cancellation
as in Theorem 4.2.22 (printed p. 52).
Source ID `voight-2021-quaternion-algebras`, SHA-256
`f6c56f6ca7b4bee139b88865a3cf045f899da59d0217618c4dc81daf19ef1ad4`.
In Corollary 14.3.7 the displayed orthogonal decompositions use
\(\langle-a\rangle\) after establishing that both forms represent \(a\).
The implemented decompositions use \(\langle a\rangle\), the line
spanned by the vector of value \(a\).
The Lean proof applies the local-to-global isotropy implication of
Theorem 26.8.24 as a hypothesis. The isometry conclusion is the exact
coordinate-space proposition already in the Library.

## Dependency check

The Lean diagnostic `8fdd2927-1bb1-42e5-b269-19868952f0c8` starts at
`Langlands.numberFieldQuadraticIsometry_of_isotropy` and traverses
constants in declaration types and values, including opaque values.
The diagnostic imported the three excluded statements to check their
names. It visited 41,290 constants and found no occurrence of
`Langlands.GroupScheme.NumberFieldHassePrincipleStatement`,
`Langlands.GroupScheme.NumberFieldGaloisHassePrincipleStatement`,
`Langlands.GroupScheme.SimplyConnectedRealPlacesCohomologyStatement`,
or the corresponding proof name prefixes. The scan also visits the types
and proof terms of the auxiliary lemmas. The project declarations in the
closure follow.

<details>
<summary>Lean declaration closure</summary>

```text
Langlands.Global.FiniteCompletion
Langlands.Global.FinitePlace
Langlands.Global.InfinitePlace
Langlands.Global.Place
Langlands.Global.placeCompletion
Langlands.Global.placeCompletion._proof_1
Langlands.Global.placeCompletion.isField
Langlands.Global.placeCompletion.isField.match_1_1
Langlands.Global.placeCompletion.match_1
Langlands.NumberFieldQuadraticIsometryReductionStatement
Langlands.NumberFieldQuadraticIsometryStatement
Langlands.NumberFieldQuadraticIsometryStatement._proof_1
Langlands.NumberFieldQuadraticIsometryStatement._proof_2
Langlands.NumberFieldQuadraticIsometryStatement._proof_3
Langlands.NumberFieldQuadraticIsotropyStatement
Langlands.NumberFieldQuadraticIsotropyStatement._proof_1
Langlands.NumberFieldQuadraticIsotropyStatement._proof_2
Langlands.NumberFieldQuadraticIsotropyStatement._proof_3
Langlands.QuadraticIsometryReduction.instInvertibleOfNat_langlands
Langlands.QuadraticIsometryReduction.instInvertibleOfNat_langlands._proof_1
Langlands.numberFieldQuadraticIsometry_of_isotropy
Langlands.quadraticForm_equivalent_of_prod_smul_sq
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.equivalent_of_local_equivalent
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendIsometry
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendIsometry._proof_1
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendIsometry._proof_2
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendIsometry._proof_3
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendIsometry._proof_4
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendIsometry._proof_5
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendIsometry._proof_6
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendLineProduct
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendLineProduct._proof_1
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendLineProduct._proof_2
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendLineProduct._proof_3
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendLineProduct._proof_4
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendLineProduct._proof_5
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendLineProduct._proof_6
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.extendLineProduct._proof_7
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.finrank_lineComplement
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.finrank_lineComplement._proof_1_1
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.lineComplement
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.lineComplement_nondegenerate
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.lineProduct_nondegenerate
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.polarBilin_isRefl
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.polar_self_ne_zero
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.represents_of_isotropic_lineProduct
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.represents_of_local_equivalent
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.splitLine
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.splitLine._proof_1
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.splitLine._proof_2
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.splitLine._proof_3
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.splitLine._proof_4
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.splitLine._proof_5
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.splitLine._proof_6
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.splitLine._proof_7
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.splitLine._proof_8
_private.Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction.0.Langlands.QuadraticIsometryReduction.splitLine._proof_9
_private.Langlands.LinearAlgebra.QuadraticWittCancellation.0.Langlands.exists_isometryEquiv_of_eq_nonzero_value
_private.Langlands.LinearAlgebra.QuadraticWittCancellation.0.Langlands.fst_apply_eq_zero_of_fix_axis
_private.Langlands.LinearAlgebra.QuadraticWittCancellation.0.Langlands.polarReflection
_private.Langlands.LinearAlgebra.QuadraticWittCancellation.0.Langlands.polarReflection._proof_1
_private.Langlands.LinearAlgebra.QuadraticWittCancellation.0.Langlands.polarReflection._proof_2
_private.Langlands.LinearAlgebra.QuadraticWittCancellation.0.Langlands.polarReflection._proof_3
_private.Langlands.LinearAlgebra.QuadraticWittCancellation.0.Langlands.polarReflection._proof_4
_private.Langlands.LinearAlgebra.QuadraticWittCancellation.0.Langlands.polarReflection._proof_5
_private.Langlands.LinearAlgebra.QuadraticWittCancellation.0.Langlands.polarReflection._proof_6
_private.Langlands.LinearAlgebra.QuadraticWittCancellation.0.Langlands.polarReflection_apply
_private.Langlands.LinearAlgebra.QuadraticWittCancellation.0.Langlands.polar_prod_axis
```

</details>
