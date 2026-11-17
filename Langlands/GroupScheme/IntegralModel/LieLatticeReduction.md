# Reduction of the Lie lattice to the special fibre

Let `R` be a local domain with fraction field `K` (`IsFractionRing R K`),
maximal ideal `𝔪` and residue field `𝔣 = IsLocalRing.ResidueField R`. Let `G`
be a group scheme over `Spec K` and let `M : IntegralModel R K G` be a supplied
integral model with group scheme `𝒢 = M.group` over `Spec R`. The Library's
`Langlands.GroupScheme.IntegralModel.LieLattice` gives the actual Lie module
`M.LieModule = Lie(𝒢)` (the dual-number identity kernel with coefficients in
`R`) and the Lie lattice `M.lieLattice ⊆ GenericLie R G`. The Library's
`Langlands.GroupScheme.IntegralModelReduction` gives the special fibre
`M.specialFibre = 𝒢_𝔣`. It is the pullback of `𝒢` along
`residueBaseMap R = Spec (R → 𝔣)`.

This module defines the reduction map `Lie(𝒢) → Lie(𝒢_𝔣)`. For a smooth model
it proves that the map is surjective with kernel `𝔪 • Lie(𝒢)`. It also
proves that reduction commutes with differentials of model homomorphisms.
The module `Langlands.BruhatTits.IntegralModels.ReductiveQuotientLie` uses
these results for Kaletha–Prasad §13.3.2.

## Differentials on `GenericLie`

`GenericLie R G` is the Library's type synonym for `Lie(G)`, which is
`Additive (lieKernel G K)` regarded as an `R`-module. `GenericLie.map R f` is
the differential of `f : G ⟶ H` on it. Assume `[IsAffineHom G.X.hom]`, and
likewise for `H` and `L`.

- `GenericLie.map_id`: `map R (𝟙 G) X = X`.
- `GenericLie.map_comp`: `map R (f ≫ g) X = map R g (map R f X)`. This is the
  `GenericLie` form of the Library's `Lie.targetMapLinear_comp`. The proof
  compares the underlying dual-number points; there the claim is associativity
  of composition.
- `GenericLie.map_surjective`: if the differential `Lie.targetMapLinear f K`
  is surjective, then `map R f` is surjective.

## The special fibre and the residue-field Lie kernel

- `IntegralModel.specialFibre_isAffineHom` (instance): `M.specialFibre` is
  affine over `Spec 𝔣`. The proof is that a pullback of the affine morphism
  `M.group.X.hom` is affine. Until now the Library proved this fact only inside
  individual files, by `let`, `local instance` or `private instance`
  declarations.
- `IntegralModel.algebraSpecialFibre_isAffineHom` (local instance, by the same
  argument): the pullback of `𝒢` along `algebraBaseMap R 𝔣` is affine over
  `Spec 𝔣`.
- `IntegralModel.algebraBaseMap_residueField`: the base morphism
  `algebraBaseMap R 𝔣` of the `R`-algebra `𝔣` equals `residueBaseMap R`. The
  proof rewrites with `IsLocalRing.ResidueField.algebraMap_eq`.
- `IntegralModel.specialFibreAlgebraBaseIso M`: the pullback of `𝒢` along
  `algebraBaseMap R 𝔣` is isomorphic to `M.specialFibre`, by `eqToIso` of the
  previous equality. The Library's Lie base-change comparisons use the first
  form of the pullback, and the special fibre is defined by the second.
- `IntegralModel.residueLieEquiv M`, assuming `[IsAffineHom G.X.hom]`: an
  `𝔣`-linear isomorphism `Lie(𝒢, 𝔣) ≃ Lie(𝒢_𝔣)`. Here
  `Lie(𝒢, 𝔣) = Additive (lieKernel M.group 𝔣)` is the identity kernel of `𝒢`
  with coefficients in `𝔣`, and `Lie(𝒢_𝔣)` is `GenericLie R M.specialFibre`. It
  is the composite of three maps. The first is the inverse of the Library's
  pullback comparison `Lie.kernelBaseChangeLinearEquiv R 𝔣 M.group 𝔣`. The
  second is the Library's `lieKernelLinearEquiv` of
  `specialFibreAlgebraBaseIso`. The third is `(GenericLie.equiv R _).symm`.

## The reduction map

- `IntegralModel.lieReduction M : M.LieModule →ₗ[R] GenericLie R M.specialFibre`
  applies coefficient change along `Algebra.ofId R 𝔣` (the Library's
  `lieKernelMapLinear`) and then `residueLieEquiv`. `lieReduction_apply` unfolds
  it, by `rfl`.
- `IntegralModel.smul_top_le_ker_lieReduction`:
  `𝔪 • ⊤ ≤ LinearMap.ker M.lieReduction`. For `r ∈ 𝔪`, the scalar `r` acts on
  `GenericLie R _` through its image in `𝔣`, which is `0`.

Assume now that `M` is smooth (`hM : M.IsSmooth`).

- `IntegralModel.specialFibreLieEquiv hM : 𝔣 ⊗[R] Lie(𝒢) ≃ₗ[𝔣] Lie(𝒢_𝔣)` is
  the Library's smooth scalar extension `Lie.smoothKernelScalarExtension M.group 𝔣`
  followed by `residueLieEquiv`.
- `IntegralModel.specialFibreLieEquiv_tmul`:
  `specialFibreLieEquiv hM (a ⊗ₜ X) = a • M.lieReduction X`.
  `lieReduction_eq_specialFibreLieEquiv` is the case `a = 1`.
- `IntegralModel.lieReduction_surjective hM`: reduction is surjective. Every
  element of `𝔣 ⊗[R] Lie(𝒢)` is a pure tensor `1 ⊗ₜ X`, because `R → 𝔣` is
  surjective (Mathlib's `TensorProduct.mk_surjective`).
- `IntegralModel.ker_lieReduction hM`:
  `LinearMap.ker M.lieReduction = 𝔪 • ⊤`. By `specialFibreLieEquiv_tmul`, an
  element `X` of the kernel satisfies `1 ⊗ₜ X = 0` in `𝔣 ⊗[R] Lie(𝒢)`. The
  proof then shows, for any `R`-module `N` and `Y : N`, that `1 ⊗ₜ Y = 0`
  implies `Y ∈ 𝔪 • ⊤`. To do this it applies the `𝔣`-linear map
  `𝔣 ⊗[R] N → N ⧸ 𝔪 • ⊤` given by Mathlib's
  `TensorProduct.AlgebraTensorModule.lift`. That map sends `1 ⊗ₜ Y` to the class
  of `Y`.

## Naturality

Let `φ : M.Hom N f` be a model homomorphism over `f : G ⟶ H`, with
`[IsAffineHom H.X.hom]`. Its special-fibre map is the Library's
`φ.specialFibreMap`.

- `IntegralModel.Hom.specialFibreAlgebraBaseIso_naturality`:
  `specialFibreAlgebraBaseIso` commutes with `φ`. The proof generalizes the base
  morphism together with its equality to `residueBaseMap R`, then substitutes.
- `IntegralModel.Hom.residueLieEquiv_naturality`: `residueLieEquiv` takes the
  differential of `φ.hom` with coefficients in `𝔣` to the differential
  `GenericLie.map R φ.specialFibreMap`. The proof uses the Library's
  `Lie.kernelBaseChangeLinearEquiv_target` and then the previous lemma.
- `IntegralModel.Hom.lieReduction_naturality`:
  `N.lieReduction (Lie.targetMapLinear φ.hom R X) =
  GenericLie.map R φ.specialFibreMap (M.lieReduction X)`. The proof uses the
  Library's `lieKernelTargetLinear_map` (differentials commute with coefficient
  change) and the previous lemma.

## Relation to the literature

For a smooth affine group scheme `𝒢` over a discrete valuation ring, the
identification `Lie(𝒢) ⊗ 𝔣 = Lie(𝒢_𝔣)` is standard. Kaletha–Prasad use it
without separate proof in §13.3.2 (printed p. 470; PDF p. 501), where
`Lie(Gred_x)` is written as `cok(g_{x,0+} ⊗_o f → g_{x,0} ⊗_o f)`. This module
proves the identification, with the kernel `𝔪 • Lie(𝒢)` of the reduction
map, for every supplied smooth model over a local domain. The corrections of
1 November 2024 have no entry for §13.3.

## Provenance

Derived. The Lean route is internal and composed from published Library
constructions. These are `Lie.kernelBaseChangeLinearEquiv` and
`Lie.kernelBaseChangeLinearEquiv_target` (`Lie.BaseChange`,
`Lie.LinearBaseChangeNaturality`), `Lie.smoothKernelScalarExtension` and
`Lie.smoothKernelScalarExtension_tmul` (`Lie.SmoothScalarExtension`),
`lieKernelMapLinear` (`Lie.AffineModule`), `lieKernelTargetLinear_map`
(`Lie.KernelTargetMaps`), `lieKernelLinearEquiv`
(`Dynamic.AdjointDeterminantModelIndependence`), `GenericLie`,
`GenericLie.map` and `IntegralModel.LieModule` (`IntegralModel.LieLattice`),
and `residueBaseMap`, `specialFibre` and `Hom.specialFibreMap`
(`IntegralModelReduction`). The kernel computation uses Mathlib's
`TensorProduct.AlgebraTensorModule.lift` and `LinearMap.ringLmapEquivSelf`. No
external code is adapted.

## Not claimed

- The Lie bracket is not treated: all maps are linear maps of modules.
- Nothing is said about non-smooth models beyond `smul_top_le_ker_lieReduction`.
- No comparison with the Lie algebra of the generic fibre is made here beyond
  what `IntegralModel.LieLattice` already provides.
