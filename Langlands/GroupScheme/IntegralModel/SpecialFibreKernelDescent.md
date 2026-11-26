# Descent of smooth connected unipotent special-fibre kernels

This module shows that the kernel conditions of KP Axiom 4.1.22(1) descend
along a local change of coefficients. The kernel must be smooth, connected and
unipotent. The main application changes coefficients from `↥𝒪[F]` to the
integers of the maximal unramified extension.

## Declarations

- `IsSmoothConnectedUnipotent X`, for a group scheme `X` over `Spec k` with `k`
  a field, is the conjunction `Smooth X.X.hom ∧ ConnectedSpace X.X.left ∧
  IsUnipotent X`. These are the three kernel conditions of KP Axiom 4.1.22(1),
  in the same form as `RelativeComponentModelHom.HasSmoothConnectedUnipotentKernel`
  and the conclusion of `UnramifiedModelKernelStatement`.
- `IsSmoothConnectedUnipotent.of_iso`: the property transfers backward along an
  isomorphism `X ≅ Y`.
- `IsSmoothConnectedUnipotent.of_baseChange`: let `k → K` be a field
  extension and `X` a group scheme over `Spec k` with `IsAffineHom X.X.hom`. If
  the base change of `X` to `Spec K` has the property, then so does `X`.
- `IntegralModel.residueExtensionMap A`: for a local homomorphism `R → A` of
  local rings, the map `Spec 𝓀_A ⟶ Spec 𝓀_R` of spectra of residue fields.
- `IntegralModel.residueBaseMap_comp_algebraMap`: the square of spectra formed
  by the residue maps of `R` and `A`, `Spec.algebraMap R A` and
  `residueExtensionMap A` commutes.
- `IntegralModel.isSmoothConnectedUnipotent_kernel_of_square`: let
  `b ≫ a = b' ≫ a'` be two factorizations of a map `Spec k ⟶ S₀`, and let
  `φ : X ⟶ Y` be a homomorphism of group schemes over `S₀`. If the kernel of
  the base change of `φ` along `a` and then `b` has the property, then so does
  the kernel of its base change along `a'` and then `b'`.
- `IntegralModel.Hom.isSmoothConnectedUnipotent_kernel_of_baseChangeCoefficients`:
  take models `M`, `N` over a local domain `R` with fraction field `K`, a model
  homomorphism `ψ : M.Hom N f`, and a local domain `A` with fraction field `L`.
  Suppose `R → A` is a local homomorphism compatible with `K → L`. If the
  special-fibre kernel of `ψ.baseChangeCoefficients A L` has the property, then
  so does `kernel ψ.specialFibreMap`.
- `IntegralModel.Hom.ofGenericEq ψ h`: the same integral homomorphism `ψ.hom`,
  regarded as a model homomorphism over `f'` when `h : f = f'`.
  `Hom.ofGenericEq_hom` records that the underlying homomorphism is unchanged.
- `IntegralModel.Hom.isSmoothConnectedUnipotent_kernel_of_baseChangeUnramified`:
  let `F` be a nonarchimedean local field and let `M₀`, `N₀` be models of `G₀`
  over `↥𝒪[F]`. Suppose every model homomorphism
  `M₀.baseChangeUnramified ⟶ N₀.baseChangeUnramified` with identity generic
  fibre has a smooth, connected and unipotent special-fibre kernel. Then every
  `ψ : M₀.Hom N₀ (𝟙 G₀)` has a smooth, connected and unipotent special-fibre
  kernel.

The last theorem transfers the kernel property from
`UnramifiedModelKernelStatement` to models over `↥𝒪[F]`.

## Proof

The kernel transport uses the Library isomorphism `kernelSquareIso q q' e d h`
(module `Langlands.GroupScheme.KernelSquareTransport`): for homomorphisms
`q : G ⟶ H`, `q' : G' ⟶ H'` and isomorphisms `e : G ≅ G'`, `d : H ≅ H'` with
`e.hom ≫ q' = q ≫ d.hom`, it identifies `kernel q ≅ kernel q'`.

`of_iso` transfers smoothness with `smooth_of_over_iso`, connectedness with the
homeomorphism `Scheme.homeoOfIso` of underlying spaces, and unipotence with
`IsUnipotent.of_iso`. `of_baseChange` uses the Library fpqc facts
`fieldExtension_fpqc` for `Spec K ⟶ Spec k`. Smoothness then descends by
`smooth_of_baseChange`, connectedness by `connectedSpace_of_baseChange`, and
unipotence by `IsUnipotent.of_baseChange`, which needs `IsAffineHom`.

`residueBaseMap_comp_algebraMap` reduces, by `Spec.map_comp`, to the equality of
ring maps `R → 𝓀_A` through `A` and through `𝓀_R`. These agree
definitionally, and `congr 1` closes the goal.

For `isSmoothConnectedUnipotent_kernel_of_square`, the Library iso
`baseChangeCompIso` and its naturality `baseChangeCompIso_hom_naturality`
identify the iterated base change of `φ` along `a` and `b` with the base change
along `b ≫ a`. `kernelSquareIso`, applied to the reversed naturality equation,
then transports the kernel property. One
rewrites `b ≫ a = b' ≫ a'` and transports back along `a'`, `b'` the same way.

`Hom.isSmoothConnectedUnipotent_kernel_of_baseChangeCoefficients` applies
`Hom.specialFibreKernel_properties_of_baseChange` to the three properties in
`IsSmoothConnectedUnipotent`. The residue-field base change identifies the
special-fibre kernels, and smoothness, connectedness and unipotence descend
along the field extension.

The unramified corollary installs the coefficient algebra
`↥𝒪[F] → fixedFieldIntegers F` and its scalar tower, using the same
`Valuation.HasExtension` instances that define `IntegralModel.baseChangeUnramified`.
The local-homomorphism instance comes from Mathlib's
`Valuation.HasExtension.instIsLocalHomValuationInteger`. The theorem applies the
hypothesis to `ψ.baseChangeCoefficients` reindexed along
`(baseChange _).map (𝟙 G₀) = 𝟙 _` (`Functor.map_id`), then applies the previous
theorem.

## Provenance

KP prove the kernel properties of Axiom 4.1.22(1) over the maximal unramified
extension (Kaletha–Prasad, *Bruhat–Tits theory: a new approach*,
Proposition 8.4.15). They then descend by unramified descent (§9.5 and
Axiom 4.1.22). The descent step uses only that smoothness, connectedness and
unipotence descend along field extensions. This module formalizes that step.
The kernel-isomorphism and base-change bookkeeping is internal.
