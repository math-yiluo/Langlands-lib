# Base change of Lie algebras and of Lie lattices

Lie algebras are the Library's dual-number kernels: for a group scheme `G` over `Spec K`,
`Lie(G) = ker(G(K[ε]) → G(K))` (`lieKernel G K`), and `GenericLie R G` is the type synonym of
`Additive (lieKernel G K)` carrying the `R`-module structure through `R → K`
(`IntegralModel.LieLattice`). For an integral model `M : IntegralModel R K G`, `M.lieMap` is
the injective `R`-linear map `Lie(𝒢) → Lie(G)` and `M.lieLattice` its range.

This module defines the base change map of Lie algebras for a field extension `L/K` and
proves that it carries the Lie lattice of an integral model into the Lie lattice of the
base-changed model. Over a nonarchimedean local field `F`, this is the inclusion
`𝔤(F) ⊂ 𝔤(K)`, `K` the maximal unramified extension, restricted to the lattices: it carries
`Lie(𝒢)` into `Lie(𝒢_{𝒪_K})`.

## The base change map

Let `L/K` be a field extension (`[Algebra K L]`) and `G` an affine group over `K`. The instance
`GenericLie.baseChange_isAffineHom` says that the base change
`G_L = (GroupScheme.baseChange (Spec.algebraMap K L)).obj G` is affine over `Spec L` (it is a
pullback of `G.X.hom`).

- `GenericLie.baseChangeMap R S L G : GenericLie R G →+ GenericLie S G_L`. An element
  `X ∈ ker(G(K[ε]) → G(K))` is sent by the coefficient change `K[ε] → L[ε]` to
  `G(L[ε])` and then regarded as an `L[ε]`-point of the scheme pullback `G_L`; this is the
  Library's `Lie.kernelFieldExtension`. The rings `R` (with `[Algebra R K]`) and `S` (with
  `[Algebra S L]`) are the phantom parameters of the two type synonyms and only select their
  module structures. `baseChangeMap_apply` unfolds the definition, by `rfl`.
- `baseChangeMap_smul`: `baseChangeMap (c • X) = algebraMap K L c • baseChangeMap X` for
  `c ∈ K`, from the semilinearity of `lieKernelMapLinear` and the linearity of the pullback
  comparison `Lie.kernelBaseChangeLinearEquiv`.

Under the Library's `Lie.schemeScalarExtension G : L ⊗[K] Lie(G) ≃ₗ[L] Lie(G_L)` (for `G`
locally of finite type) the map is `X ↦ 1 ⊗ X` (`Lie.schemeScalarExtension_one_tmul`), and
`Lie.kernelFieldExtension_injective` shows that it is injective; this module uses neither.

## Lie lattices

Let `R` be a domain with fraction field `K`, `M : IntegralModel R K G`, and let `A` be a domain
with fraction field `L` such that the square `R → A → L`, `R → K → L` commutes
(`[IsScalarTower R A L] [IsScalarTower R K L]`). `M.baseChange A L` is the Library's base change
of the model, an integral model over `A` of `G_L`, whose generic identification is composed
from the pullback squares and `M.genericIso` (`IntegralModel.BaseChange`).

- `affineBaseChangeEquiv_baseChangeGenericIso`: for a point `w` of the generic fibre of `𝒢_A`
  with values in an `L`-algebra `B`, its image in `G_L`, regarded as a point of `G` and then
  through `M.genericIso⁻¹` as a point of `𝒢`, is the point of `𝒢` obtained by the two
  projections of the pullbacks. This is `IntegralModel.baseChangeGenericIso_hom_fst` on points.
- `affinePoints_ext`: a point of `G` with values in a `K`-algebra is determined by the
  corresponding point of `𝒢` (the comparisons are bijections and `M.genericIso` is an
  isomorphism).
- `lieMap_baseChangeMap`: for `X ∈ Lie(𝒢)`,
  `(M.baseChange A L).lieMap (X_A) = baseChangeMap (M.lieMap X)`, where `X_A` is the coefficient
  change of `X` along `R → A` (`Lie.kernelFieldExtension` for the ring map `R → A`). Both
  sides are sent to the point of `𝒢` with values in `L[ε]` obtained from `X` by the coefficient
  change `R[ε] → L[ε]`; the two routes `R → A → L` and `R → K → L` agree by the scalar towers.
- `baseChangeMap_mem_lieLattice`: `Y ∈ M.lieLattice` implies
  `baseChangeMap Y ∈ (M.baseChange A L).lieLattice`;
  `map_baseChangeMap_lieLattice_le` is the same as an inclusion of additive subgroups.
- `baseChangeMap_mem_lieLattice_baseChangeUnramified`: for a nonarchimedean local field `F`,
  `K = inertiaFixedField F` its maximal unramified extension in `F^sep` and
  `M : IntegralModel 𝒪[F] F G`, the base change map carries `M.lieLattice` into the Lie lattice
  of `M.baseChangeUnramified`, the base change of `M` to the integers `fixedFieldIntegers F` of
  `K` (`IntegralModel.UnramifiedModelDescent`), with the same algebra structure
  `𝒪[F] → fixedFieldIntegers F` as there.

No smoothness or flatness of the model is used.

## Comparison with Kaletha–Prasad

Kaletha–Prasad §13.3.3 (printed p. 470; PDF p. 501) lets `𝔤(K)_{x,r}` be "the `O`-lattice in
`𝔤(K)` which is the Lie algebra of the group scheme `(𝒢_{x,r})_O`" and states
`𝔤_{x,r} = (𝔤(K)_{x,r})^Γ`; Theorem 13.5.1(1) (printed p. 474; PDF p. 505) asks for the
Moy–Prasad isomorphism to be compatible with unramified extensions. Both use the inclusion
`𝔤(k) ⊂ 𝔤(K) = 𝔤(k) ⊗_k K` and the inclusion `Lie(𝒢) ⊂ Lie(𝒢_O)` of the Lie algebra of an
`𝔬`-model into that of its base change. `GenericLie.baseChangeMap` is the first map on the
Library's Lie algebras, and `baseChangeMap_mem_lieLattice_baseChangeUnramified` is the second
inclusion, for any model over `𝒪[F]`.

The corrections of 1 November 2024 have no entry for §13.3 or for Theorem 13.5.1.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`: §13.3.3 (printed p. 470;
  PDF p. 501) and Theorem 13.5.1 (printed p. 474; PDF p. 505).
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024,
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

## Provenance

Derived. The base change of Lie algebras along a field extension and the compatibility of the
Lie lattice of an integral model with base change of coefficients are standard; KP use them
without a separate statement. The Lean construction is a composite of the Library's
`Lie.kernelFieldExtension` (`Lie.FieldExtension`), `Lie.affineBaseChangeEquiv`,
`Lie.kernelBaseChangeEquiv` and their naturality (`Lie.BaseChange`), `IntegralModel.lieMap`
(`IntegralModel.LieLattice`) and `IntegralModel.baseChange` with
`baseChangeGenericIso_hom_fst` (`IntegralModel.BaseChange`). No external code is adapted.

## Not claimed

- The image of `Lie(𝒢)` is not shown to span `Lie(𝒢_A)` over `A`, and no isomorphism
  `A ⊗_R Lie(𝒢) ≅ Lie(𝒢_A)` is stated.
- No statement about Galois-fixed points (`𝔤_{x,r} = (𝔤(K)_{x,r})^Γ`) is made.
