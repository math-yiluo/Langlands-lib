# Smoothness of the integral functions

Module `Langlands.GroupScheme.IntegralModel.Smoothening.Smoothness`. This is a
helper module of the proof of
`Langlands.GroupScheme.IntegralModel.SmootheningStatement`.

Let `R` be a discrete valuation ring with residue field `k` and fraction field
`K`, `A` a commutative `R`-algebra and `B = integralFunctions R K A ⊆ K ⊗[R] A`.
The module shows that `B` is smooth over `R` when `k` is algebraically closed,
`A` is a Hopf algebra with smooth generic fibre `K ⊗[R] A`, and `B` is a
finitely generated `R`-algebra. Finite generation is a hypothesis here. It is
the content of `IntegralFunctionsFiniteTypeStatement` (KP Theorem A.6.2), which
is proved separately. The argument is internal to this project. It follows the
fibrewise proof of smoothness of Néron smoothenings: the special fibre is
reduced, hence smooth, being a group over an algebraically closed field, and the
generic fibre does not change.

## A reduced group over an algebraically closed field

`smooth_of_isReduced_of_isAlgClosed`: let `k` be an algebraically closed field
and `H` a commutative Hopf algebra over `k` that is reduced and of finite type
over `k`. Then `H` is smooth over `k`.

The proof applies the Library theorem
`Langlands.GroupScheme.RationalPointClosure.smooth_of_grpObj_of_isAlgClosed` to
the group scheme `(hopfSpec k).obj (op H)`. That theorem is a copy of a private
Mathlib lemma: a reduced group scheme locally of finite type over an
algebraically closed field is smooth. The structure morphism of this group
scheme is `Spec.map (algebraMap k H)`. `HasRingHomProperty.Spec_iff` turns
finite type of `H` into `LocallyOfFiniteType` of this morphism, and turns
`Smooth` of the morphism back into `Algebra.Smooth k H`. The source scheme
`Spec H` is reduced because `H` is.

## Transfer between base fields

`formallySmooth_tensor_of_algHom`: let `f : F →ₐ[R] L` be a map of
`R`-algebras. If `F ⊗[R] B` is formally smooth over `F`, then `L ⊗[R] B` is
formally smooth over `L`. View `L` as an `F`-algebra through `f`. Then
`L ⊗[F] (F ⊗[R] B)` is formally smooth over `L` by base change, and it is
isomorphic to `L ⊗[R] B` by `Algebra.TensorProduct.cancelBaseChange`.

## The generic fibre

Assume that `R` is a domain with fraction field `K`.

- `genericMul : K ⊗[R] B →ₐ[K] K ⊗[R] A` sends `c ⊗ b` to `c • b`, using the
  inclusion `B ⊆ K ⊗[R] A`.
- `genericMap : K ⊗[R] A →ₐ[K] K ⊗[R] B` is `id ⊗ incl`.
- `genericMul_genericMap`: `genericMul ∘ genericMap` is the identity, since
  `c ⊗ a ↦ c ⊗ incl a ↦ c • (1 ⊗ a) = c ⊗ a`.
- `genericMap_surjective`: for `c ⊗ b`, choose `s ≠ 0` and `a` with
  `s • b = 1 ⊗ a` (`exists_smul_eq_one_tmul`). Then `c ⊗ b` is the image of
  `(c / s) ⊗ a`.
- `genericEquiv : K ⊗[R] A ≃ₐ[K] K ⊗[R] B` is `genericMap`, which is bijective
  by the two previous lemmas.

## The special fibre and the main theorem

Assume that `R` is a discrete valuation ring.

- `isReduced_residueField_tensor`: `k ⊗[R] B` is reduced. Every element is
  `1 ⊗ b` (`exists_one_tmul_eq`). If `(1 ⊗ b)^n = 1 ⊗ b^n = 0`, then for every
  `R`-point `φ` of `A`, the reduction of `point φ b` has `n`-th power zero
  (apply `reduceForm (point φ)`), so `point φ b` lies in the maximal ideal. By
  `detectsMaximal_point`, `b` lies in `𝔪 B`, so `1 ⊗ b = 0`
  (`one_tmul_eq_zero_iff`).
- `residueFieldToMaximal : k →ₐ[R] κ(𝔪)` is the map from `R ⧸ 𝔪` to the residue
  field `(maximalIdeal R).ResidueField` of the localization at `𝔪`.
- `smooth_of_smooth_fibres` (fibre criterion over a discrete valuation ring):
  let `C : Type u` be a flat `R`-algebra of finite type such that `K ⊗[R] C` is
  formally smooth over `K` and `k ⊗[R] C` is formally smooth over `k`. Then `C`
  is smooth over `R`. Indeed, `C` is finitely presented
  (`Algebra.FinitePresentation.of_finiteType`, `R` noetherian). Mathlib's
  fibrewise criterion `Algebra.Smooth.of_formallySmooth_fiber` reduces
  smoothness to formal smoothness of `κ(p) ⊗[R] C` over `κ(p)` for every prime
  `p` of `R`. Either `p = ⊥` or, by `Ideal.IsPrime.isMaximal` and
  `IsLocalRing.eq_maximalIdeal`, `p = 𝔪`.
  - For `p = ⊥`: transfer formal smoothness of `K ⊗[R] C` along the
    `R`-isomorphism `IsLocalization.algEquiv` from `K` to `κ(⊥)`, another
    fraction field of `R` (`formallySmooth_tensor_of_algHom`).
  - For `p = 𝔪`: transfer formal smoothness of `k ⊗[R] C` along
    `residueFieldToMaximal`.
- `smooth_integralFunctions`: assume that `k` is algebraically closed, that `A`
  is a Hopf algebra with `K ⊗[R] A` smooth over `K`, and that `B` is of finite
  type over `R`. Then `B` is smooth over `R`. Apply `smooth_of_smooth_fibres`
  to `C = B`, which is flat (instance `instFlat` of the Hopf module):
  - the generic fibre `K ⊗[R] B ≅ K ⊗[R] A` is formally smooth over `K`
    (`genericEquiv`);
  - the special fibre `k ⊗[R] B` is a reduced Hopf algebra of finite type over
    the algebraically closed field `k` (Mathlib's base-change Hopf structure on
    `k ⊗[R] B`). So it is smooth by `smooth_of_isReduced_of_isAlgClosed`.

## Library and Mathlib results used

- Library: `Langlands.GroupScheme.RationalPointClosure.smooth_of_grpObj_of_isAlgClosed`.
- Mathlib: `hopfSpec`, `HasRingHomProperty.Spec_iff`,
  `RingHom.finiteType_algebraMap`, `RingHom.smooth_algebraMap`,
  `Algebra.TensorProduct.cancelBaseChange`,
  `Algebra.FormallySmooth.of_equiv`, `Algebra.Smooth.of_formallySmooth_fiber`,
  `Algebra.FinitePresentation.of_finiteType`, `Ideal.IsPrime.isMaximal`,
  `IsLocalRing.eq_maximalIdeal`, `IsLocalization.algEquiv`.
