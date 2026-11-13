# Actual special linear contragredient automorphism

Author: Worker 195.

This module constructs the inverse-transpose automorphism `g ↦ (g⁻¹)ᵀ` of
the actual special linear group scheme `SpecialLinear.groupScheme n R` over
`Spec R`. It proves its formula on points over every test scheme, its
involutivity, its compatibility with the published general-linear
contragredient through the inclusion `SL_n ⟶ GL_n`, and its restriction to
the published diagonal torus of `SL_{n+1}`, which is inversion. All new
declarations lie in `Langlands.GroupScheme.SpecialLinear`.

## Matrix automorphism

Let `n : Type` have `Fintype n` and `DecidableEq n`, and let `A : Type u`
be any commutative ring. Empty `n` and the zero ring are allowed.

Three auxiliary identities about Mathlib's
`Matrix.SpecialLinearGroup.transpose` are proved entrywise:

- `transpose_mul_eq`: `(g * h)ᵀ = hᵀ * gᵀ`;
- `transpose_inv_eq`: `(g⁻¹)ᵀ = (gᵀ)⁻¹`, using that the inverse in
  `Matrix.SpecialLinearGroup` is the adjugate and that the adjugate commutes
  with transposition;
- `transpose_transpose_eq`: `(gᵀ)ᵀ = g`.

`matrixContragredient n A` is the multiplicative equivalence of
`Matrix.SpecialLinearGroup n A` with itself whose forward and inverse
functions are both `g ↦ transpose (g⁻¹)`. It is its own inverse by the second
and third identities, and it preserves multiplication because inversion and
transposition each reverse products.

- `matrixContragredient_apply` and `matrixContragredient_coe` give its value
  and its underlying matrix `((g⁻¹ : SL) : Matrix)ᵀ`;
- `matrixContragredient_coe_eq_adjugate` records that this matrix is
  `(adjugate g)ᵀ`, by definition of the inverse in the special linear group;
- `matrixContragredient_symm` identifies the inverse equivalence with the
  same equivalence, and `matrixContragredient_involutive` is the
  double-application identity;
- `toGL_matrixContragredient` proves that the image in `GL n A` of the
  special-linear contragredient is the published
  `GeneralLinear.matrixContragredient n A` of the image;
- `matrixContragredient_map` proves, for every ring homomorphism
  `f : A →+* B` with `B : Type v` in an independent universe, that
  `Matrix.SpecialLinearGroup.map f` commutes with the contragredient.

## Scheme automorphism

Now let `R : CommRingCat.{u}`. For every `T : Over (Spec R)`,
`contragredientPoints n R T` transports `matrixContragredient n Γ(T.left, ⊤)`
through the published multiplicative equivalence
`SpecialLinear.pointsEquiv n R T` between points
`T ⟶ (groupScheme n R).X` and determinant-one matrices over the global
sections of `T`.

- `pointsEquiv_contragredientPoints` is its matrix formula;
- `contragredientPoints_naturality` states that for `a : T' ⟶ T` the
  operation commutes with precomposition by `a`; the proof applies
  injectivity of `pointsEquiv`, the published `pointsEquiv_naturality`, and
  `matrixContragredient_map`;
- `contragredientPoints_involutive` reduces to matrix involutivity.

`contragredientIso n R : groupScheme n R ≅ groupScheme n R` is the actual
isomorphism of group schemes constructed by the published
`Langlands.GroupScheme.isoOfPoints` from this natural family of
multiplicative equivalences. Its existence is not an extra premise.

- `comp_contragredientIso_hom`: postcomposing a point `x` with the underlying
  scheme morphism `(contragredientIso n R).hom.hom.hom` gives
  `contragredientPoints n R T x`;
- `pointsEquiv_contragredientIso'`: the determinant-one matrix of
  `x ≫ (contragredientIso n R).hom.hom.hom` is
  `matrixContragredient n Γ(T.left, ⊤) (pointsEquiv n R T x)`;
- `pointsEquiv_contragredientIso`: the same statement after coercion to
  matrices, namely the matrix of the image point equals the transpose of the
  matrix of the inverse `(pointsEquiv n R T x)⁻¹`;
- `contragredientIso_hom_comp_hom`: composing the forward group-scheme
  morphism with itself is the identity `𝟙 (groupScheme n R)`; the proof uses
  the published `hom_ext_points` and pointwise involutivity;
- `contragredientIso_inv`: consequently the inverse morphism equals the
  forward morphism;
- `contragredientIso_hom_comp_inclusion`: the published inclusion
  `SpecialLinear.inclusion n R : groupScheme n R ⟶ GeneralLinear.groupScheme n R`
  intertwines `contragredientIso n R` with the published
  `GeneralLinear.contragredientIso n R`; the proof compares points through
  `GeneralLinear.pointsEquiv`, `pointsEquiv_inclusion`, and
  `toGL_matrixContragredient`.

## Restriction to the diagonal torus

In the namespace `SpecialLinear.FinSucc`, fix `n : ℕ` and use the published
diagonal torus `diagonalTorus n R` from the split torus
`splitTorus (Spec R) (ULift (Fin n))` into `groupScheme (Fin (n + 1)) R`.
By the published `pointsEquiv_diagonalTorus`, a point with unit coordinates
`τ` goes to `torusMatrix τ`, the diagonal matrix with entries
`torusEntry τ p`.

- `torusMatrix_inv`: `torusMatrix τ⁻¹ = (torusMatrix τ)⁻¹`, since the
  published `torusMatrixHom` is a group homomorphism;
- `matrixContragredient_torusMatrix`: inverse transpose sends
  `torusMatrix τ` to `torusMatrix τ⁻¹`, since a diagonal matrix equals its
  transpose;
- `diagonalTorus_comp_contragredientIso_hom`:

  ```text
  diagonalTorus n R ≫ (contragredientIso (Fin (n + 1)) R).hom =
    CommGroupScheme.groupHom (-𝟙 (splitTorus.commGroupScheme (Spec R) (ULift (Fin n))))
      ≫ diagonalTorus n R.
  ```

  Here `-𝟙` is negation of the identity in the additive group of
  endomorphisms of the commutative split torus, and `CommGroupScheme.groupHom`
  views it as a morphism of group schemes. The proof checks points: by the
  published `comp_groupHom_zsmul` with `m = -1`, postcomposition with this
  morphism is pointwise inversion, and the matrix formulas above identify
  both sides with `torusMatrix τ⁻¹`.

## Provenance and scope

This is internal content: the classical inverse-transpose automorphism of
`SL_n`, written for the Library's actual special linear group scheme. It
specializes the published general-linear construction
`Langlands/GroupScheme/GeneralLinearContragredient` and is linked to it by
`toGL_matrixContragredient` and `contragredientIso_hom_comp_inclusion`. The
construction uses only the published `SpecialLinear.pointsEquiv`, its
naturality, `isoOfPoints`, `hom_ext_points`, the published diagonal torus of
`Langlands/GroupScheme/Reductive/SpecialLinearTorus`, and Mathlib matrix
identities. No external source identification is asserted.

The base is affine and the coordinate type is finite; the scheme and its
test schemes use the same universe `u`, while the matrix coefficient
naturality lemma allows independent ring universes. No field, smoothness,
reductivity, or positive-rank hypothesis is required. The module does not
identify the contragredient with a diagram automorphism or a pinning-preserving
automorphism, and it does not compute its action on root groups.
