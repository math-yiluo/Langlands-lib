# The Lie lattice of an integral group model

Let `R` be a commutative domain with fraction field `K` (`IsFractionRing R K`).
Let `G` be a group scheme over `Spec K` whose structure morphism is affine, and
let `M : IntegralModel R K G` be a supplied integral model. Such a model is an
affine, flat, finite-type group scheme `𝒢 = M.group` over `Spec R` together with
a chosen isomorphism `M.genericIso : 𝒢_K ≅ G`. Lie algebras are the Library's
actual dual-number identity kernels `lieKernel`, that is
`Lie(G) = ker(G(K[ε]) → G(K))`, with their module structures from
`Lie.AffineModule`.

This module constructs the `R`-linear map `Lie(𝒢) → Lie(G)`. It proves that the
map is injective and that, for a smooth model, its image is an `R`-lattice in
`Lie(G)`. This is the lattice assertion of Kaletha–Prasad §13.3.1 for any
supplied smooth model. The construction is natural for model homomorphisms.

## The generic Lie algebra as an `R`-module

`GenericLie R G` is a type synonym for `Additive (lieKernel G K)`. It carries the
original `K`-module structure, an `R`-module structure through `algebraMap R K`
(`Module.compHom`), and the instance `IsScalarTower R K (GenericLie R G)`. The
ring `R` is a phantom parameter that only selects the `R`-module structure. The
synonym exists so that `R`-submodules of `Lie(G)` and Mathlib's
`Submodule.IsLattice K` can be stated without a global `R`-module instance on
`Additive (lieKernel G K)`.

- `GenericLie.smul_def`: `r • X = algebraMap R K r • X`, by `rfl`.
- `GenericLie.equiv`: the identity `K`-linear equivalence with
  `Additive (lieKernel G K)`.
- `GenericLie.map R f`: for `f : G ⟶ H` with both groups affine, the
  differential `Lie.targetMapLinear f K`, transported to the synonyms and
  restricted to `R`-scalars. `GenericLie.map_apply` unfolds it, by `rfl`.

## The Lie map and the Lie lattice

Two affineness facts come first. The instance
`IntegralModel.genericFibre_isAffineHom` says that the actual generic fibre
`M.genericFibre` is affine over `Spec K`, because it is a pullback of the affine
model. The theorem `IntegralModel.generic_isAffineHom M` says that `G` itself is
affine over `Spec K`, because `M.genericIso.inv` is an isomorphism over `Spec K`.
The constructions below take `[IsAffineHom G.X.hom]` as a hypothesis; this
theorem discharges it.

- `M.LieModule` is `Additive (lieKernel M.group R)`, the actual Lie module
  `Lie(𝒢)` over `R`.
- `M.genericLieEquiv : Lie(𝒢_K) ≃ₗ[K] GenericLie R G` is the inverse of the
  pullback comparison `Lie.kernelBaseChangeLinearEquiv R K M.group K`, followed by
  `lieKernelLinearEquiv M.genericIso K`, the differential of the supplied generic
  isomorphism.
- `M.lieMap : M.LieModule →ₗ[R] GenericLie R G` first changes coefficients along
  `R → K` with `lieKernelMapLinear M.group (Algebra.ofId R K)`, then applies
  `M.genericLieEquiv`. `lieMap_apply` records this formula.
- `lieMap_injective`: the Lie map is injective. The proof uses only that
  `R → K` is injective (so `R[ε] → K[ε]` is injective) and that the model is
  affine, through `Lie.affineMap_jointly_injective`. Smoothness and flatness are
  not used.
- `M.lieLattice : Submodule R (GenericLie R G)` is the range of `M.lieMap`.
  `mem_lieLattice` unfolds membership, and
  `lieLatticeEquiv : M.LieModule ≃ₗ[R] M.lieLattice` is the equivalence given by
  injectivity.

## Smooth models

Let `hM : M.IsSmooth`.

- `lieBaseChangeEquiv hM : K ⊗[R] M.LieModule ≃ₗ[K] GenericLie R G` is the
  Library's smooth scalar extension `Lie.smoothKernelScalarExtension M.group K`
  followed by `M.genericLieEquiv`.
- `lieBaseChangeEquiv_tmul`: `a ⊗ X` maps to `a • M.lieMap X`.
- `lieLattice_isLattice hM : Submodule.IsLattice K M.lieLattice`. In Mathlib's
  definition this means that `M.lieLattice` is a finitely generated
  `R`-submodule whose `K`-span is all of `Lie(G)`. Finite generation is the image
  of `Lie.finite_lieKernel_of_smooth`, the finiteness of the actual Lie module of
  a smooth affine group. The spanning property holds because
  `lieBaseChangeEquiv hM` is surjective: induction on tensors puts every image
  in the `K`-span of the lattice, using `lieBaseChangeEquiv_tmul`.

## Model homomorphisms

Let `N : IntegralModel R K H` with `H` affine, `f : G ⟶ H`, and
`φ : M.Hom N f` a model homomorphism extending `f`.

- `Hom.kernelBaseChange_symm_target`: the inverse pullback comparison commutes
  with the differential of `φ.hom` and of its base change. This is the linear
  form of the Library's `Lie.kernelBaseChangeEquiv_target`.
- `Hom.lieMap_naturality`:
  `N.lieMap (Lie.targetMapLinear φ.hom R X) = GenericLie.map R f (M.lieMap X)`.
  The proof moves the differential of `φ.hom` past coefficient change
  (`lieKernelTargetLinear_map`) and past the pullback comparison. It then uses
  the compatibility square `φ.generic_comm` on underlying morphisms.
- `Hom.map_lieLattice_le`:
  `M.lieLattice.map (GenericLie.map R f) ≤ N.lieLattice`.

## Comparison with Kaletha–Prasad

Kaletha–Prasad, §13.3.1 (printed p. 470; PDF p. 501), begins: for `x ∈ B` and
`r ≥ 0`, let `𝒢_{x,r}` be the group scheme attached to the constant concave
function `r` in §8.5. "Let `𝔤_{x,r}` be the Lie algebra of this group scheme,
it is an `𝔬`-lattice in the `k`-vector space `𝔤(k)`." There `𝒢_{x,r}` is a
smooth affine group scheme over `𝔬` with generic fibre `G`, and `𝔤 = Lie(G)`.

This module proves that assertion for an arbitrary supplied smooth integral
model `M`, over an arbitrary domain `R` with fraction field `K`; in KP,
`R = 𝔬` and `K = k`. Here "lattice in `𝔤(k)`" is read as the image of `Lie(𝒢)`
under the natural injective map `M.lieMap`. KP Remark 2.10.8 (printed p. 123;
PDF p. 154) describes this identification: for a group model `𝒳` of a smooth
group `X`, `Lie(𝒳) ⊂ Lie(X)`, and the natural map `Lie(𝒳) ⊗_𝔬 k → Lie(X)` is an
isomorphism. KP works there with derivations and the cotangent space `ω_{𝒳,e}`.
This module works with the Library's dual-number kernels instead. It proves the
inclusion for every affine model (`lieMap_injective`) and the isomorphism only
for smooth models (`lieBaseChangeEquiv`).

KP recalls on printed p. 515 (PDF p. 546) that a lattice in a finite-dimensional
`k`-vector space `X` is a finitely generated `𝔬`-submodule of `X` that generates
`X` over `k`. This is Mathlib's `Submodule.IsLattice K`, which asks for a
finitely generated submodule with full `K`-span. When `R` is a principal ideal
domain, as `𝔬` is in KP, Mathlib's `Submodule.IsLattice.free` then shows that
the lattice is `R`-free. This module does not restate that fact.

The corrections of 1 November 2024 have no entry for §13.3; their Chapter 13
items concern Proposition 13.5.2(1), 13.6.2 and Theorem 13.8.5.

## Provenance

Derived. The injectivity of `Lie(𝒢) → Lie(G)`, the lattice property for smooth
models and the naturality are standard facts. KP §13.3.1 states the lattice
property for the models `𝒢_{x,r}` without a separate proof; the general
identification is KP Remark 2.10.8. The Lean route through dual-number kernels
and the smooth scalar extension is internal. The module is a composite of the
Library's actual Lie-kernel constructions:
`lieKernelMapLinear` and `Lie.affineMap_jointly_injective` (`Lie.AffineModule`),
`Lie.kernelBaseChangeLinearEquiv` (`Lie.BaseChange`),
`Lie.kernelBaseChangeEquiv_target` (`Lie.FieldExtension`),
`lieKernelLinearEquiv` (`Dynamic.AdjointDeterminantModelIndependence`),
`Lie.targetMapLinear` and `lieKernelTargetLinear_map` (`Lie.KernelTargetMaps`),
`Lie.smoothKernelScalarExtension` (`Lie.SmoothScalarExtension`), and
`Lie.finite_lieKernel_of_smooth` (`Lie.SmoothFiniteProjective`), together with
Mathlib's `Submodule.IsLattice`. No external code is adapted.

## Not claimed

- The concave-function group schemes `𝒢_{x,r}` of KP §8.5 are not constructed
  here, and `M.lieLattice` is not identified with KP's `𝔤_{x,r}` for any model.
- The identity `𝔤_{x,r+n} = 𝔪^n 𝔤_{x,r}` (KP Proposition 8.5.16), the extension
  of the filtration to all real `r`, the dual lattices `𝔤*_{x,r}`, and
  KP 13.3.2–13.3.4 (the quotient `𝔤_{x,0}/𝔤_{x,0+}`, the description of
  `𝔤_{x,r}` by root subgroups, and the action of `𝒢_x^0` on `𝔤_{x,r}`) are not
  formalized.
- The adjoint action is not treated: no statement says that integral points of
  the model preserve `M.lieLattice`.
- Without smoothness, only injectivity is proved. Finite generation, the
  spanning property of `M.lieLattice` and the isomorphism
  `K ⊗[R] Lie(𝒢) ≃ Lie(G)` are proved only for smooth models, although KP
  Remark 2.10.8 states the isomorphism for any group model of a smooth group.
- `lieLattice_isLattice` is a theorem, not a registered instance, because it
  needs the smoothness hypothesis.
