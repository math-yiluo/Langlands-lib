# Derivations into an extended ideal under flat base change

Namespace `Langlands.AlgebraicGeometry.SmoothLifting`. This file is pure
commutative algebra. The rings are `A → P → C` with
`IsScalarTower A P C`.

- `kaehlerEquivC`: the universal property of differentials,
  `Derivation A P M ≃ₗ[C] (Ω[P⁄A] →ₗ[P] M)`. Here `M` is a `C`-module
  with compatible `P`- and `A`-actions. It is Mathlib's
  `KaehlerDifferential.linearMapEquivDerivation`, upgraded to a
  `C`-linear equivalence.
- `derivationEquivHom`: the composite with
  `LinearMap.liftBaseChangeEquiv`. It identifies derivations with
  `C ⊗[P] Ω[P⁄A] →ₗ[C] M`, by `d ↦ (1 ⊗ D p ↦ d p)`. The formulas are
  `derivationEquivHom_one_tmul` and `derivationEquivHom_symm_apply`.
- For a `C`-algebra `T`, an ideal `J` of `C`, and an ideal `J'` of `T` with
  `J.map (algebraMap C T) = J'`:
  - `idealMapP` is the `P`-linear map `J → J'` given by
    `j ↦ algebraMap C T j`.
  - `derMap A P J J' hJ` is the `C`-linear map that composes derivations
    with `idealMapP`.
- `isBaseChange_derMap`: assume `T` is flat over `C`, and `P` is
  formally smooth and essentially of finite type over `A`. Then
  `IsBaseChange T (derMap A P J J' hJ)`.

  Proof. Mathlib gives `Module.FinitePresentation P Ω[P⁄A]`, so
  `ω = C ⊗[P] Ω[P⁄A]` is finitely presented over `C`. The map is then the
  following composite of equivalences:
  - `Module.FinitePresentation.isBaseChange_map`: `Hom_C(ω, -)` commutes
    with flat base change;
  - the Library equivalence
    `Deformation.ElementaryKernelTensor.idealTensorEquiv`, which gives
    `T ⊗[C] J ≃ J T` for flat `T`;
  - `LinearMap.liftBaseChangeEquiv`;
  - `derivationEquivHom`.

  The composite is checked on pure tensors.

Provenance: this is an internal algebraic lemma of the lifting of
homomorphisms from groups of multiplicative type through nilpotent
thickenings. It is the module-theoretic heart of the identification of
square-zero reduction kernels with `Hom(ω, J)`.
