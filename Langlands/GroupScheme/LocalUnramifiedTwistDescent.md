# Twisting points over the maximal unramified extension

Authors: Worker 5015.

This module proves supporting lemmas for
`Langlands.GroupScheme.LocalSimplyConnectedUnramifiedIntegralTwistReductionStatement`. They
concern a group scheme `G` over a nonarchimedean local field `F` with an integral model
`M : IntegralModel 𝒪[F] F G`. Write `L₀ = LocalGalois.Separable.inertiaFixedField F` for the
maximal unramified extension of `F` inside `SeparableClosure F`.

The main result, `GaloisCocycle.isTrivial_of_unramified_integral_twist`, says the following.
Let a point `h` of `G` over the infinite extension `L₀` (or over any normal subextension of it)
twist the Galois values of a cocycle into points with integral coordinates for a smooth model
with connected special fibre. Then the cocycle is trivial. The published finite-level criterion
`GaloisCocycle.isTrivial_of_integral_twist` (module `Langlands.GroupScheme.LocalUnramifiedIntegralCocycle`)
needs the twisting point over a finite Galois unramified extension. This module descends `h` to
such an extension.

All declarations live in the namespace `Langlands.GroupScheme`. The module proves no new
proposition definitions.

## Declarations

### Integral coordinates (namespace `IntegralModel`)

The module uses two local instances. They make the valuation ring
`LocalGalois.Separable.fixedFieldIntegers F` of `L₀` an `𝒪[F]`-algebra, with the scalar tower
`𝒪[F] → fixedFieldIntegers F → L₀`. Both come from Mathlib's `Valuation.HasExtension` instances
for the valuation of `F` and the published `fixedFieldValuation F`. They have the explicit
names `unramifiedTwistIntegerAlgebra` and `unramifiedTwistIntegerScalarTower` so that
this module can be imported together with `IntegralModel.UnramifiedIntegralPointAction`
without generated declaration-name collisions. Their instance bodies are unchanged.

| Declaration | Content |
|---|---|
| `mem_range_fixedFieldIntegers_iff_isIntegral` | An element `y ∈ L₀` lies in the image of `fixedFieldIntegers F` exactly when `y` is integral over `𝒪[F]`. |
| `mem_baseChangeUnramified_integralPoints_iff` | Let `p ∈ G(L₀)`. The point corresponding to `p` under `baseChangeCoeffEquiv F L₀ G` lies in `M.baseChangeUnramified.integralPoints` exactly when `M.HasIntegralCoordinates L₀ p`. |
| `hasIntegralCoordinates_of_relativeExtend` | General integral model `M : IntegralModel R K G` with `R` a domain with fraction field `K`, and a tower of fields `K → E → L` with compatible `R`-algebra structures. If the extension `GaloisPoint.relativeExtend K E L G p` of `p ∈ G(E)` has integral coordinates for `M`, then so does `p`. |

`IntegralModel.baseChangeUnramified` is the published base change of `M` to the valuation ring
of `L₀`. So `mem_baseChangeUnramified_integralPoints_iff` says that, over `L₀`, the integral
points of the base-changed model are the points with integral coordinates in the sense of
`IntegralModel.HasIntegralCoordinates`.

### Cocycles (namespace `GaloisCocycle`)

| Declaration | Content |
|---|---|
| `exists_finiteDimensional_isGalois_between` | Let `L` and `K₀` be intermediate fields of `SeparableClosure F / F` with `L/F` normal, `K₀/F` finite and `K₀ ≤ L`. Then some intermediate field `E'` is finite and Galois over `F` with `K₀ ≤ E' ≤ L`. |
| `isTrivial_of_integral_twist_of_tower` | The tower step, stated below. |
| `isTrivial_of_unramified_integral_twist` | The main result, stated below. |

**`isTrivial_of_integral_twist_of_tower`.** Let `G` be affine. Let `M` be smooth over `𝒪[F]`
with connected special fibre: the base change of `M.group` along `Spec 𝓀[F] → Spec 𝒪[F]` has a
connected underlying space. Let `L` be an intermediate field of `SeparableClosure F / F`,
normal over `F`. Let `E` be a field, finite and Galois over `F`. Let `E'` be an intermediate
field, finite and Galois over `F`, with `E' ≤ L₀`. Assume a tower of algebras
`F → E → E' → L` with all scalar-tower instances. Let `ξ : Cocycle G (GaloisCocycle.cover F E)`
and `h' ∈ G(E')`. Write `ext_{A,B}` for `GaloisPoint.relativeExtend F A B G`. Assume that for
every `σ ∈ Gal(L/F)` the point

`ext_{E',L}(h')⁻¹ * ext_{E,L}(value ξ (σ|E)) * σ(ext_{E',L}(h'))`

has integral coordinates for `M` over `L`. Here `σ|E = σ.restrictNormal E` and
`σ(-) = GaloisPoint.conjugate F L G σ`. Then `ξ.IsTrivial`.

**`isTrivial_of_unramified_integral_twist`.** Let `G` be affine and locally of finite type over
`F`, and let `M` be smooth with connected special fibre as above. Let `L` be an intermediate field
of `SeparableClosure F / F`, normal over `F`, with `L ≤ L₀`. Let `E` be a field, finite and Galois
over `F`, with an `F`-algebra map to `L` (`[Algebra E L] [IsScalarTower F E L]`). Let
`ξ : Cocycle G (GaloisCocycle.cover F E)` and `h ∈ G(L)`. Assume that for every
`σ ∈ Gal(L/F)` the point

`h⁻¹ * ext_{E,L}(value ξ (σ|E)) * σ(h)`

has integral coordinates for `M` over `L`. Then `ξ.IsTrivial`.

## The implemented proofs

**`mem_range_fixedFieldIntegers_iff_isIntegral`.** Integrality over `𝒪[F]` is membership in
`integralClosure 𝒪[F] L₀`. The published `LocalUnramified.integers`,
`LocalUnramified.mem_integers_iff` and `fixedFieldIntegers_eq` identify this with membership in
`fixedFieldIntegers F`.

**`mem_baseChangeUnramified_integralPoints_iff`.** The published
`mem_coefficientIntegralPoints_iff` turns membership in `integralPoints` into membership in the
coefficient integral points of `M.baseChange (fixedFieldIntegers F) L₀`. The published
`mem_baseChange_coefficientIntegralPoints_iff_genericCoordinates` says this holds when every
generic coordinate lies in the image of `fixedFieldIntegers F`. The previous lemma turns this
into integrality over `𝒪[F]`.

**`hasIntegralCoordinates_of_relativeExtend`.** By `GaloisPoint.coordinates_relativeExtend`,
the coordinates of the extended point are the images of the coordinates of `p` under the
injective `R`-algebra map `E → L`. Integrality is reflected by injective algebra maps
(Mathlib's `isIntegral_algHom_iff`).

**`exists_finiteDimensional_isGalois_between`.** Take `E' = normalClosure F K₀ (SeparableClosure F)`.
It is finite and normal. It is separable because `SeparableClosure F` is separable over `F`.
It contains `K₀` (`le_normalClosure`), and it lies in `L` because `L/F` is normal
(`normalClosure_le_iff_of_normal`).

**`isTrivial_of_integral_twist_of_tower`.**

1. `E'/E` is finite Galois (`IsGalois.tower_top_of_isGalois`).
2. Let `ξ' = ξ.refine (coverMap F E E')`. Its Galois values are given by the published
   `value_refine`: `value ξ' σ' = ext_{E,E'}(value ξ (σ'|E))`.
3. For `σ' ∈ Gal(E'/F)` let `σ = σ'.liftNormal L`. Then `σ|E = σ'|E`
   (`IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply` and `AlgEquiv.restrict_liftNormal`).
   Also `ext_{E',L} ∘ ext_{E,E'} = ext_{E,L}`: compare coordinates with
   `GaloisPoint.coordinates_relativeExtend`. The published `relativeExtend_conjugate_lift`
   moves `σ'` past `ext_{E',L}`. Together with multiplicativity of `ext_{E',L}` this gives

   `ext_{E',L}(h'⁻¹ * value ξ' σ' * σ'(h')) = ext_{E',L}(h')⁻¹ * ext_{E,L}(value ξ (σ|E)) * σ(ext_{E',L}(h'))`.

4. By the hypothesis at `σ` the right side has integral coordinates over `L`. By
   `hasIntegralCoordinates_of_relativeExtend`, the point `h'⁻¹ * value ξ' σ' * σ'(h')` has
   integral coordinates over `E'`.
5. The published `isTrivial_of_integral_twist` shows that `ξ'` is trivial. The published
   `isTrivial_of_refine` shows that `ξ` is trivial.

The proof is compiled with `set_option backward.isDefEq.respectTransparency true` for this
declaration only. With the module's default setting the last step timed out in instance
unification.

**`isTrivial_of_unramified_integral_twist`.**

1. The coordinate ring of `G` is a finitely generated `F`-algebra; pick a finite generating set
   `s`. Let `c : AffineCoordinateRing F G.X →ₐ[F] L` be the coordinates of `h`
   (`GaloisPoint.coordinates F G L h`).
2. Let `K₀` be the compositum, inside `SeparableClosure F`, of the image of `E` and the field
   generated by the values `c a`, `a ∈ s`. It is finite over `F`: the image of `E` is finite,
   and the values are finitely many separable algebraic elements. It lies in `L`.
3. `exists_finiteDimensional_isGalois_between` gives a finite Galois `E'` with `K₀ ≤ E' ≤ L`.
   This makes `E → E' → L` a tower of `F`-algebras.
4. All values `c a` lie in `E'`, because `E'` contains the values on the generators. So `c`
   factors through `E'` and defines `h' ∈ G(E')` with `ext_{E',L}(h') = h`. The equality is
   checked on coordinates with `GaloisPoint.coordinates_relativeExtend`.
5. Rewrite the hypothesis with `h = ext_{E',L}(h')`, note `E' ≤ L ≤ L₀`, and apply
   `isTrivial_of_integral_twist_of_tower`.

## Provenance

Provenance: derived. These lemmas implement the last step of the proof of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Theorem 10.6.1 (printed pp. 397–398, PDF
pp. 428–429), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`. There the twisting
element `g ∈ G(K)`, `K` the maximal unramified extension, moves a cocycle into an Iwahori subgroup
`I = G_C^0(O)`, and Lemma 8.1.4 then trivializes it. The source works with continuous cohomology
of `Gal(K/k)`. The Library's cocycles live on finite covers, so this module descends the twisting
element to a finite Galois unramified level, where the finite-level criterion
`GaloisCocycle.isTrivial_of_integral_twist` applies. The descent steps (finitely many
coordinates, normal closure, refinement of cocycles) are standard and not stated in the source.
