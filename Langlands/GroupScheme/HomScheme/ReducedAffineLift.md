# Reductions of affine points through a homomorphism over the reduced base

Namespace `Langlands.GroupScheme.HomScheme`.

## Setting

- `R : CommRingCat` and an arbitrary ideal `I` of `R`.
- Group schemes `H, G` over `Spec R`. No affineness, flatness or smoothness
  is assumed.
- `r := Spec.algebraMap R (R ⧸ I)`.
- A homomorphism of base-changed group schemes
  `f₀ : (GroupScheme.baseChange r).obj H ⟶ (GroupScheme.baseChange r).obj G`.
- An `R`-algebra `A : CommAlgCat R` and the extended ideal
  `J_A := I.map (algebraMap R A)`.
- `A ⧸ J_A` carries Mathlib's canonical `R ⧸ I`-algebra structure
  (`Ideal.Quotient.algebraQuotientMapQuotient`).

## Declarations

- `reducedAffineHom I f₀ A : H.affinePoints A →* Lie.AffinePoints G (A ⧸ J_A)`
  is the composite of four group homomorphisms:
  1. reduce a point modulo `J_A`
     (`Lie.NonaffineKernel.reduction H J_A`);
  2. view it as a point of `H_{R/I}` with coefficients `A ⧸ J_A`, via the
     Library equivalence `affinePointsBaseChangeMulEquiv`;
  3. apply `f₀` (`affinePointsTarget`);
  4. read the result back in `G(A ⧸ J_A)`
     (`affinePointsBaseChangeMulEquiv`, inverse direction).
- `reducedAffineHom_of_lift` is the compatibility with lifts. Let
  `s : H.X ⟶ G.X` be any morphism over `Spec R` with
  `(Over.pullback r).map s = f₀.hom.hom`. The morphism `s` need not be a
  homomorphism. Then for every `h : H.affinePoints A`:

  ```text
  Lie.NonaffineKernel.reduction G J_A (h ≫ s) = reducedAffineHom I f₀ A h
  ```
- `reducedAffineHom_naturality` is naturality in the coefficient algebra.
  Let `φ : A ⟶ B` and let `reducedMap I φ : A ⧸ J_A →ₐ[R] B ⧸ J_B` be the
  induced map, with `extended_le_comap` its well-definedness. Then:

  ```text
  reducedAffineHom I f₀ B (H.affinePointMap φ h) =
    Lie.affineMap G (reducedMap I φ) (reducedAffineHom I f₀ A h)
  ```
- Auxiliary formulas for the underlying scheme maps:
  `reducedAffineHom_left`, `baseChange_point_fst`, `baseChange_point_snd`.

All proofs compare underlying scheme morphisms. They use the pullback
projections and `affinePointsBaseChangeMulEquiv_symm_left`. The axioms are
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Internal adapter for Task 6989, written by Worker 496 at the request of
Worker 880. It feeds the reduction-of-lift actions and defect cochains in
the cohomological proof of SGA 3 IX 3.6.
