# Scalar extension and the algebra tensor product

This module contains the pure algebra comparison extracted unchanged from
[TildePullback](../AlgebraicGeometry/Modules/TildePullback.md), authored by
Worker 274 and prepared with Worker 405. All five declarations retain their
names in `Langlands.Scheme.Modules`, their signatures and their implementations.
They are shared by scheme pullback and ring-level cohomology constructions.

Here `A B : CommRingCat.{u}` carry `[Algebra A B]`, and
`M : ModuleCat.{u} A`. There are no finiteness, flatness or nonzero-ring
hypotheses.

For `φ := CommRingCat.ofHom (algebraMap A B)` the scalar extension
`(ModuleCat.extendScalars φ.hom).obj M` and the algebra tensor product `B ⊗[A] M` are different
`B`-modules in Lean. The first uses the `A`-module structure on `B` obtained by restricting
scalars along `φ.hom`. The second uses the `A`-module structure that comes from the `Algebra A B`
instance. The two structures are equal only propositionally (`Algebra.smul_def`), so the two
tensor products are not definitionally equal. The module therefore builds an explicit
`B`-linear equivalence.

- `extendScalarsToAlgebraTensor A B M` and `algebraTensorToExtendScalars A B M` are the two
  additive maps `b ⊗ₜ m ↦ b ⊗ₜ m`. Each is built with `TensorProduct.liftAddHom`. The
  `A`-balancedness condition is checked with `Algebra.smul_def` and `TensorProduct.smul_tmul`.
- `extendScalarsAlgebraEquiv A B M` is the `B`-linear equivalence
  `(extendScalars φ.hom).obj M ≃ₗ[B] B ⊗[A] M` with these two maps. `B`-linearity and both
  inverse laws are proved by `TensorProduct.inductionOn`. On pure tensors they hold by `rfl`.
- `extendScalarsAlgebraIso A B M` is the same equivalence as an isomorphism
  `(extendScalars φ.hom).obj M ≅ ModuleCat.of B (B ⊗[A] M)` in `ModuleCat B`.
  `extendScalarsAlgebraIso_hom_tmul` records `b ⊗ₜ[A, φ.hom] m ↦ b ⊗ₜ[A] m` by `rfl`.

These are internal tensor-product adapters using Mathlib's universal property
and induction principle. Extracting them introduces no new mathematical claim.
