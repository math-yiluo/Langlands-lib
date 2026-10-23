# Harris complex group points on arbitrary test schemes

This module is an internal derivation from `ComplexGroupNaturality`,
`ComplexCocharacterMatrices`, and their imported group-scheme constructions.
It constructs a natural multiplicative equivalence on **every** complex test
scheme for the actual iterated complex pullback of the rational Harris group.
The construction uses the existing group scheme and its proved real model
comparison. No representing scheme or point equivalence is supplied as new data.

## Inputs and the actual source

The inputs are `CentralSimpleUnitaryData E K A n`, denoted `D`, and
`HarrisSignatureCharts D.toSecondKindInvolution n Φ`, denoted `C`. The typeclasses
retain number fields `E` and `K`, total reality of `E`, total complexity of `K`,
the quadratic extension `K/E`, the algebra structures on `A`, and their indicated
scalar towers. These are the same inputs as in `ComplexCocharacterMatrices`.
The charts supply actual real algebra identifications and their signature,
involution, and center compatibilities; they do not assume a complex group
splitting. The finite bases used below are `D.rationalBasis` and
`D.totallyRealBasis`, already constructed from the central-simple input.

The source group scheme is `D.complexRationalGroupScheme`: pull the rational
similitude scheme back along `Spec ℝ → Spec ℚ`, then along
`Spec ℂ → Spec ℝ`. For any scheme `T` over `Spec ℂ`, put

\[
S_T=\Gamma(T,\mathcal O_T).
\]

Its real and complex algebra structures come from the actual structure morphism,
using the scalar-tower instance in `ComplexCocharacterMatrices`. In Lean this
relative real algebra is `AlgebraInvolution.complexTestAlgebra T`. The test scheme
need not be affine, reduced, connected, or nonempty.

## The point equivalence and coordinate formulas

`D.complexGroupPointsEquiv C T` is a multiplicative equivalence

\[
\operatorname{Hom}_{\operatorname{Spec}\mathbb C}
 (T,G_{\mathbb Q}\times_{\mathbb Q}\mathbb R\times_{\mathbb R}\mathbb C)
\;\simeq\;
\left(\prod_{\tau:E\to\mathbb R}
 \operatorname{Matrix}_n(S_T)^\times\right)\times S_T^\times.
\]

Its three factors are:

1. Postcomposition with the actual complex pullback of
   `D.realGroupSchemeIso`, obtained by applying group-valued Yoneda to that
   isomorphism.
2. `complexSimilitudePointsEquiv` for the real algebra
   `ℝ ⊗[ℚ] A`, identifying these scheme points with similitudes in
   `S_T ⊗[ℝ] (ℝ ⊗[ℚ] A)`.
3. `C.iteratedScalarGroupSplitting D.totallyRealBasis S_T`.

Each factor is a constructed multiplicative equivalence, so this composition
supplies both inverse laws and compatibility with the actual scheme group law.
There is one common scalar unit, not one multiplier for each embedding.

`complexGroupPointsEquiv_matrix` identifies its first matrix at `τ` with the
first component of the existing `D.complexPointMatrices C T g τ`. In particular,
the coordinate system is the one already used for the Harris cocharacter.
`complexGroupPointsEquiv_multiplier` identifies its scalar factor with the
multiplier of the actual scalar-extended similitude obtained in step 2.
Both proofs reduce to the definitions (the latter uses extensionality of units).

If the resulting point is `(a,c)`, `complexGroupPointsEquiv_second` proves that
the second matrix in `complexPointMatrices` is

\[
(c\,1_n)\,H_{r_\tau}\,(a_\tau^{-1})^{\mathsf T}\,H_{r_\tau},
\qquad
r_\tau=\begin{cases}n-1&\tau=C.\mathrm{distinguished},\\n&\text{otherwise}.\end{cases}
\]

Here `H_r` is the existing diagonal signature matrix and the transpose fixes
coefficients in `S_T`. This formula is obtained by applying the explicit inverse
formula for `harrisSimilitudesEquiv` to the image of the given point and cancelling
the inverse equivalence. It imposes no conjugation on the test ring.

## Naturality and the full point presheaf

`complexTestAlgebraMap a` is the actual complex algebra map on global sections
induced by `a : T' ⟶ T`. `complexSimilitudePointsEquiv_naturality` proves that
restriction of complex pullback points becomes the tensor coefficient map for
its restriction to real scalars. The proof combines the naturality of the
pullback point adjunction with `Corepresented.pointsEquiv_naturality`; the
remaining section map identity is definitional.

`complexGroupPointsEquiv_naturality` then says that precomposing `g` by `a`
corresponds to `ComplexMatrix.splitGroupMap` for `a.left.appTop.hom`. This applies
the induced ring map entrywise to the matrix units and to the scalar unit. Its
proof reassociates the postcomposition in step 1, applies the preceding lemma,
and uses the proved naturality of the iterated scalar group splitting.

Finally, `D.complexGroupPointsIso C` packages these equivalences as an isomorphism
of group-valued presheaves on all schemes over `Spec ℂ`. Its target is
`Corepresented.globalPointsFunctor (ComplexMatrix.splitGroupFunctor n (E →+* ℝ))`:
the already constructed split algebra functor evaluated on relative global
sections. Naturality is precisely the preceding identity, checked on elements.

This gives the full point-presheaf comparison. This module does not construct
the general-linear group scheme or identify the target presheaf with the points
of its product with `G_m`; that explicit scheme realization is a subsequent
prerequisite and comparison. Smoothness, reductivity, Shimura level schemes, and
PEL representability are not conclusions of this module.
