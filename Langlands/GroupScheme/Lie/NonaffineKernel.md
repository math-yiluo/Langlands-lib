# Square-zero reduction kernels of arbitrary group schemes

Namespace `Langlands.GroupScheme.Lie.NonaffineKernel`. Fix
`G : GroupScheme (Spec R)` with no affineness, separatedness or smoothness
hypothesis, an `R`-algebra `A`, and an ideal `J` of `A`. The kernel
`kernel G J` of the reduction homomorphism
`reduction G J = Lie.affineMap G (Ideal.Quotient.mkₐ R J)` on actual
points `Lie.AffinePoints G A` is a normal subgroup. The reduction and its kernel use the shared
`Lie.SquareZero.reduction` and `Lie.SquareZero.kernel` definitions.

## Kernel points are lifts of the identity

- `KLift G J` is the type of global lifts, in the sense of
  `SmoothLifting.GlobalComb`, of the identity point `unit₀ G J` of
  `G(A ⧸ J)`, over `str A : Spec A ⟶ Spec R`.
- `kernelEquiv` (built from `toLift` and `ofLift`) identifies kernel points
  with these lifts. `base G J` is the identity.

## The group law is addition

Assume `SqZero J`.
- `toLift_mul`: for kernel points `x` and `y`, the lift of `x * y` is the
  sum of the lifts in `LiftModule hJ (base G J)`.
- Proof. The pair `(x, y)` is a lift on `G ⊗ G` (`pair`, determined by its
  projections, `PLift.ext`). It is the sum `(x, 1) + (1, y)`, by linearity
  of the projections (`LiftModule.lin_map`). Applying the multiplication
  `μ`, which is also linear, gives `x * 1 + 1 * y`.
- Consequently `kernel_mul_comm`.

With `[Fact (SqZero J)]` the following instances exist:
- `kernelCommGroup`;
- `kernelModule : Module A (Additive (kernel G J))`, transported along the
  additive bijection `toLM` (`toLMEquiv` is the resulting `A`-linear
  equivalence with `LiftModule`);
- `kernelQuotientModule : Module (A ⧸ J) (Additive (kernel G J))`, since
  `J` acts trivially (`kernel_isTorsionBySet`), together with
  `IsScalarTower A (A ⧸ J) _`.

## Conjugation

- `conjMor = fst * snd * fst⁻¹ : G.X ⊗ G.X ⟶ G.X` is the conjugation
  morphism.
- For an actual point `g`, the pairs `(g, x)` form lifts of `(ḡ, 1)`
  (`pairG`), and they are linear in `x` (`pairG_lin`).
- Applying `conjMor` gives `conjLift`, which is linear (`conjLift_lin`) and
  equals actual conjugation (`conjLift_toLift`).
- `kernelConjugationLinear g` is conjugation by `g` as an `A`-linear map
  on `Additive (kernel G J)`. `kernelConjugationLinear_apply` says that it
  sends `x` to `g x g⁻¹`.
  `kernelConjugationLinear_eq_of_reduction_eq` says that it depends only
  on the reduction of `g`, by commutativity of the kernel.

## Provenance

These are internal constructions for Task 6989 by Worker 496. They are the
nonaffine counterpart of the affine square-zero kernel theory used for
SGA 3, Exposé III, §2 (deformation of homomorphisms) and Exposé IX,
Théorème 3.6. The identification `Additive (kernel G (I B)) ≃ₗ[B]
B ⊗[R] Additive (kernel G I)` for smooth `G` and flat `B` is developed
separately.
