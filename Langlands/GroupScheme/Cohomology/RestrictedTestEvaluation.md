# Evaluating scalar-extended module points on restricted test algebras

Fix a commutative ring `R`, an `R`-algebra `K` (`K : CommAlgCat R`) and an arbitrary `R`-module `M`. The Library's `Cohomology.BaseChange` regards a `K`-algebra `A` as an `R`-algebra `restrictedTest K A`. It identifies `A ⊗_K (K ⊗_R M)` with `A ⊗_R M` by `scalarExtensionCancel`. This module compares that construction with tensors in `K ⊗_R (P ⊗_R M)` over an `R`-algebra `P`. Inside the module the Library's local instances `restrictedTestAlgebra` and `restrictedTestTower` are activated.

## Definitions

- `restrictedScalar K A : K →+* restrictedTest K A` is the structure map of the `K`-algebra `A`.
- `restrictedEval φ : K ⊗_R ModulePoints M P →ₗ[R] ModulePoints M (restrictedTest K A)`, for an `R`-algebra map `φ : P ⟶ restrictedTest K A`, sends `k ⊗ x` to `restrictedScalar k • φ_* x`. Here `φ_*` is the Library's `modulePointMap`.
- `constantPoints P : M →ₗ[R] ModulePoints M P` is `m ↦ 1 ⊗ m`.
- `tensorTest K P` is the `K`-algebra `K ⊗_R P`. It is a plain definition, so instance search on its restriction finds the restricted `R`-algebra structure rather than the tensor-product one.
- `tensorTestInclusion K P : P ⟶ restrictedTest K (tensorTest K P)` is `p ↦ 1 ⊗ p`.
- `tensorTestRestrict K P` is the identity of `K ⊗_R P`, viewed as an `R`-linear map out of the restricted test algebra.
- `tensorTestLift ψ : tensorTest K P ⟶ A` is the `K`-algebra map `k ⊗ p ↦ k · ψ(p)` determined by an `R`-algebra map `ψ : P ⟶ restrictedTest K A`.

## Results

- `modulePointMap_smul` states that extension of coefficients is semilinear for the test-algebra scalar action.
- `restrictedScalar_smul` states that `restrictedScalar` commutes with `R`-scalars.
- `restrictedEval_tmul` and `restrictedEval_one_tmul` give the value on pure tensors. In particular `1 ⊗ x ↦ φ_* x`.
- `restrictedEval_lTensor`: evaluating `(K ⊗ ψ_*) y` along `φ` equals evaluating `y` along `ψ ≫ φ`.
- `restrictedEval_restrictedTestMap`: for a `K`-algebra map `f : A ⟶ B`, extending the evaluation along `restrictedTestMap K f` equals evaluating along `φ ≫ restrictedTestMap K f`.
- `restrictedEval_action`: for a natural module representation `ρ` of a group scheme `H` over `Spec R` and a point `g` of `H` over `P`, acting by `φ_* g` after evaluation equals evaluating `(K ⊗ ρ_P(g)) y`. This uses the naturality of `ρ`.
- `scalarExtensionCancel_one_tmul`: the Library's cancellation map sends `1 ⊗ m'`, for `m' : K ⊗_R M`, to the evaluation of `(K ⊗ constantPoints) m'`.
- `tensorTestRestrict_scalar_mul` gives the product formula `(k ⊗ 1)(1 ⊗ p) = k ⊗ p` in restricted form.
- `restrictedEval_tensorTestInclusion_injective` and `restrictedEval_tensorTestInclusion_surjective` show that evaluation along `P → K ⊗_R P` is a bijection `K ⊗_R (P ⊗_R M) → (K ⊗_R P) ⊗_R M`. A left inverse is built from `tensorTestRestrict` and the tensor associator. Surjectivity is proved by induction on tensors.
- `tensorTestInclusion_comp_lift` states that `tensorTestLift ψ` restricts to `ψ` on `P`.

## Provenance

This is internal derived infrastructure for the flat base-change step of Conrad, *Reductive group schemes*, Proposition B.2.2 and Remark B.2.4. It moves cohomological identities proved after base change to `K` back to tensors over `K ⊗_R P`, where flat descent of range membership applies. Every statement is an elementary identity about tensor products and the Library's published base-change constructions. No source assertion is introduced.

Semilinearity under change of coefficients uses the shared affine module action lemma. [Affine module actions](AffineModuleActions.md)
