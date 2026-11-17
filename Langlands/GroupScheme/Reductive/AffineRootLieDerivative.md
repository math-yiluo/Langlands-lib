# Derivatives of root parametrizations over an arbitrary ring

Worker 163.

Module `Langlands.GroupScheme.Reductive.AffineRootLieDerivative`, namespace
`Langlands.GroupScheme.LocalSplitCell`. It works over an arbitrary commutative ring `R`
(no locality, no Noetherian hypothesis) and a group scheme `G` over `Spec R` with
`IsAffineHom G.X.hom`. It proves that a root parametrization `u : 𝔾ₐ → G` of a nonzero
root is determined by its derivative at `ε`, and that this derivative lies in the root
weight space. Consequently an automorphism of `G` that fixes the split torus and whose
Lie algebra map fixes a free root line fixes every parametrization of that root. This
is the Lie-algebra half of Conrad's uniqueness argument for pinned isomorphisms
(*Reductive group schemes*, 2014, Proposition 6.1.13(2) and Lemma 6.1.4); it is used by
[`AffinePinnedUniqueness`](AffinePinnedUniqueness.md).

## Conventions of the Library used here

- `lieKernel G A` is the kernel of `G(A[ε]) → G(A)` for an `R`-algebra `A`, written
  additively and made an `A`-module by `ε`-scaling. `Lie.targetMapLinear f A` is the
  `A`-linear map it induces from a homomorphism `f : G ⟶ H` (composition with `f`).
- `splitTorus.exponentWeightSpace I G i m` is the `R`-submodule of
  `Additive (lieKernel G R)` of vectors on which, over every `R`-algebra `A` and every
  `t ∈ (Aˣ)^I`, the adjoint action of `i(t)` is multiplication by `∏ⱼ tⱼ ^ mⱼ`.
- `IsRootParametrization i m u` (module `LocalSplitCell`) says that `u : Ga R ⟶ G`
  represents the root subgroup of the character `m`, is a closed subgroup, and satisfies
  `i(t) u(c) i(t)⁻¹ = u(m(t) c)` on all points.
- `rootPoint u Z c` is the `Z`-point `u(c)` of `G`, and `scaleHom s : Ga R ⟶ Ga R` is
  multiplication by `s ∈ R`.

## Declarations

Section `Dual`:

- `affineRootLieGaIsAffineHom` (local instance): `𝔾ₐ` over `Spec R` is affine, from
  `VectorGroup.isAffineHom_groupScheme`. It is local to this file.
- `dualTest A`: the test scheme `Spec A[ε]` over `Spec R`, for an `R`-algebra `A`.
- `dualSection A c`: the global function `c ε` on `Spec A[ε]`.
- `algSpec_map_appTop`: pulling back a global function `a` of `Spec A` along
  `Spec B → Spec A` for an `R`-algebra map `f : A → B` gives `f a`.
- `dualSection_injective`: `c ↦ c ε` is injective.
- `gaEpsilon A`: the tangent vector `ε` of `𝔾ₐ`, that is the point `ε ∈ 𝔾ₐ(A[ε])`
  reducing to `0`, as an element of `Additive (lieKernel (Ga R) A)`.
- `gaEpsilon_val`: its underlying point is `rootPoint (𝟙 (Ga R)) (dualTest A) (ε)`.
- `targetMap_gaEpsilon_val`: the derivative `du(ε) = Lie.targetMapLinear u A (gaEpsilon A)`
  of `v : Ga R ⟶ G` has underlying point `v(ε)`.
- `smul_val_of_val`: if `Y` has underlying point `v(ε)`, then `c • Y` has underlying point
  `v(c ε)`.
- `lieKernelMapLinear_val_of_val`: coefficient change along `f : A → B` sends a vector
  with underlying point `v(ε)` over `A` to one with underlying point `v(ε)` over `B`.
- `targetMap_scaleHom_comp_gaEpsilon`: `d(scaleHom s ≫ v)(ε) = s • dv(ε)`.
- `smul_gaEpsilon_injective`: if `s • ε = s' • ε` in `lieKernel (Ga R) R` then `s = s'`.

Section `Weight` (split torus `i : splitTorus (Spec R) I ⟶ G`, character `m : I → ℤ`):

- `IsRootParametrization.targetMap_gaEpsilon_mem`: for a root parametrization `u` of
  `m`, `du(ε)` lies in `exponentWeightSpace I G i m`.
- `IsRootParametrization.exists_scalar_of_ne_zero`: two parametrizations `v, w` of the
  same character `m ≠ 0` satisfy `v = scaleHom c ≫ w` for some `c ∈ R`. (No
  `IsAffineHom` hypothesis.)
- `IsRootParametrization.eq_of_targetMap_gaEpsilon`: two parametrizations of the same
  `m ≠ 0` with the same derivative at `ε` are equal.
- `IsRootParametrization.comp_eq_of_fixes_weightSpace`: if `u` parametrizes `m ≠ 0`,
  `σ : G ≅ G` satisfies `i ≫ σ.hom = i`, and `Lie.targetMapLinear σ.hom R` fixes every
  vector of `exponentWeightSpace I G i m`, then `u ≫ σ.hom = u`.
- `fixes_weightSpace_of_fixes_generator`: if `X : R ≃ₗ[R] exponentWeightSpace I G i m`
  trivializes the weight space and `Lie.targetMapLinear σ.hom R` fixes `(X 1).val`, then it
  fixes every vector of the weight space.

Outside the sections:

- `Langlands.GroupScheme.Lie.targetMapLinear_id`: `Lie.targetMapLinear (𝟙 G) A` is the
  identity linear map.

## Proofs

- The `Dual` lemmas unfold the Library's description of `lieKernel` scaling
  (`lieKernel_smul_toMul`, `lieKernelScale_val`: scaling by `c` is induced by the
  `R`-algebra map `ε ↦ c ε` of `A[ε]`) and coefficient change (`lieKernelMap_val`) as
  pullbacks along `Spec` of algebra maps, and compute them on the function `ε` by
  `algSpec_map_appTop` (from `HopfPrimitive.appTop_specMap_inv`), with `comp_rootPoint`
  for the naturality of `rootPoint`. In `targetMap_scaleHom_comp_gaEpsilon`,
  `rootPoint_scaleHom` gives `(scaleHom s ≫ v)(ε) = v(s ε)`, and the base scalar `s`
  pulled back to `A[ε]` times `ε` is `s ε`. In `smul_gaEpsilon_injective`, the coordinate
  of `𝔾ₐ` (`gaCoord`, `VectorGroup.coordinates_scalarPoint`) recovers `s ε` from
  `s • ε`, and `dualSection_injective` gives `s = s'`.
- `targetMap_gaEpsilon_mem`: after coefficient change to `A`, the adjoint action of
  `i(t)` on `u(ε)` is `i(t) u(ε) i(t)⁻¹`, where `i(t)` is pulled back to `A[ε]` along
  `A → A[ε]` (`Lie.constant`). The equivariance field of `IsRootParametrization` turns it
  into `u(m(t) ε)`, and `Corepresented.charValue_torusPt` identifies `m(t)` with
  `∏ⱼ tⱼ ^ mⱼ`; so the action is scaling by `∏ⱼ tⱼ ^ mⱼ`, which is the defining equation
  of `exponentWeightSpace`.
- `exists_scalar_of_ne_zero` applies the Library's
  `IsRootParametrization.exists_scalar` with `ν = m`: since `m ≠ 0`,
  `∑ⱼ mⱼ mⱼ = ∑ⱼ |mⱼ|²` is a positive natural number.
- `eq_of_targetMap_gaEpsilon`: write `v = scaleHom c ≫ w`. Then
  `dv(ε) = c • dw(ε) = d(scaleHom c ≫ w)(ε)`, and `Lie.targetMapLinear w R` is injective
  (`Lie.targetMapLinear_injective`, since `w` is a monomorphism), so `c • ε = 1 • ε` in
  `lieKernel (Ga R) R`, hence `c = 1` and `v = w`.
- `comp_eq_of_fixes_weightSpace`: `u ≫ σ.hom` again parametrizes `m` (the Library's
  `IsRootParametrization.comp_iso`, using `i ≫ σ.hom = i`). Its derivative is
  `dσ(du(ε)) = du(ε)` by `Lie.targetMapLinear_comp` and the hypothesis, since
  `du(ε)` is in the weight space. Conclude by `eq_of_targetMap_gaEpsilon`.
- `fixes_weightSpace_of_fixes_generator`: a vector `Y` of the weight space is
  `r • (X 1).val` with `r = X⁻¹ Y`, and `dσ` is `R`-linear.
- `Lie.targetMapLinear_id`: composition with the identity is the identity.

## Provenance

Internal. The declarations are infrastructure for the uniqueness half of the pinned
Isomorphism Theorem over an affine base
([`AffinePinnedIsomorphismTheoremStatement`](AffinePinnedIsomorphismTheoremStatement.md)).
They formalize the standard fact behind Conrad, *Reductive group schemes* (2014),
Lemma 6.1.4 (p.188) and Proposition 6.1.13(2) (pp.194–195): a parametrization of a root
group is the exponential of a trivializing section of its root space, so it is
determined by its derivative, and the Lie algebra map of a homomorphism respecting the
torus restricts to the root spaces. Every step is proved in Lean; no statement is
assumed.
