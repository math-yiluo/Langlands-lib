# Unramified integral cocycles over local fields

Authors: Worker 5015.

This module states and proves
`Langlands.GroupScheme.LocalUnramifiedIntegralCocycleVanishingStatement.{u}` at arbitrary
universe `u`. The proof is `Langlands.GroupScheme.localUnramifiedIntegralCocycleVanishing`.
It is the local-field form of the published finite-level result
`IntegralGaloisCocycleVanishingStatement` (module `Langlands.GroupScheme.IntegralGaloisCocycle`).
That result is stated for an abstract ring `R` and algebra `B`. This module applies it to
`R = 𝒪[F]` and `B = O_E` for a finite unramified Galois extension `E/F` of a nonarchimedean
local field, with coefficients in the points of an integral model inside `G(E)`.

## The statement

Let `F : Type u` be a nonarchimedean local field (`[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`), of either characteristic. Let
`G : GroupScheme (Spec F)` be a group scheme. Let `M : IntegralModel 𝒪[F] F G` be an integral
model: an affine flat finite-type group scheme `M.group` over `Spec 𝒪[F]` with a specified
isomorphism `M.genericIso` from its generic fibre to `G`. Assume:

- `M.IsSmooth`: the structure morphism of `M.group` is smooth;
- the special fibre is connected: the total space of the base change of `M.group` along
  `Spec 𝓀[F] → Spec 𝒪[F]` is a connected topological space.

Let `E : IntermediateField F (SeparableClosure F)` be finite-dimensional and Galois over `F`,
with `E ≤ LocalGalois.Separable.inertiaFixedField F`. So `E/F` is a finite unramified Galois
extension inside the Library's fixed separable closure.

The coefficient group is `G.affinePoints (CommAlgCat.of F E)`, the points `G(E)`, with their
pointwise group law. An automorphism `σ` of `E/F` acts on them by the published
`GaloisPoint.conjugate F E G σ`, which precomposes with the spectrum map of `σ`.

`M.HasIntegralCoordinates E p` (defined here, for any `K`-algebra `L` in place of `E`) says that
every regular function `a` of the model takes an `𝒪[F]`-integral value at `p`. The value is
`G.affinePointEvaluation (CommAlgCat.of F E) p (M.genericCoordinate a)`. Here the published
`M.genericCoordinate` restricts `a` to the generic fibre and transports it along
`M.genericIso`. For `L = E` the integral closure of `𝒪[F]` in `E` is the ring of integers
`O_E`. The lemmas below show that `HasIntegralCoordinates E p` holds exactly when `p` is the
image of a point of `M.group` with values in `O_E`.

The statement says: every function `c : Gal(E/F) → G(E)` that

- satisfies `c (σ * τ) = c σ * GaloisPoint.conjugate F E G σ (c τ)`, and
- has values with integral coordinates for `M`,

is a coboundary of a point `f : G(E)` with integral coordinates:
`c σ = f * (GaloisPoint.conjugate F E G σ f)⁻¹` for every `σ`. This is the coboundary
convention of the published `GaloisCocycle.value_coboundary`. In cohomological terms,
`H¹(Gal(E/F), M(O_E)) = 1`, where `M(O_E)` is viewed inside `G(E)`.

## Supporting declarations

General integral models (`R` a domain with fraction field `K`, `L` a `K`-algebra with a
compatible `R`-algebra structure):

| Declaration | Content |
|---|---|
| `IntegralModel.modelPointEquiv M L` | Multiplicative equivalence `G(L) ≃* M.group(L)`, where `M.group(L)` uses `L` as an `R`-algebra. It postcomposes with `M.genericIso.inv`, then applies the inverse of the published pullback adjunction `affinePointsBaseChangeMulEquiv R K L M.group`. |
| `modelPointEquiv_eq_genericModelPointEquiv` | Its underlying map is the published `genericModelPointEquiv`. |
| `modelPointEquiv_affinePointMap` | It intertwines a coefficient map `φ : L →ₐ[K] L` with `φ` regarded over `R`. |
| `IntegralModel.HasIntegralCoordinates M L p` | Every model regular function has an `R`-integral value at `p`. |
| `exists_affinePointMap_eq_of_mem`, `mem_of_affinePointMap_eq` | For an `R`-subalgebra `T ⊆ L`, the generic coordinates of `p` lie in `T` exactly when `modelPointEquiv L p` comes from a point of `M.group` with values in `T`. The proof uses the published `mem_range_changeRing_subalgebra_iff` and `genericModelPointEquiv_evaluation`. |
| `subalgebraPointMap`, `subalgebraPointMap_injective`, `subalgebraPointMap_conjugate` | The inclusion `M.group(T) → M.group(L)` is an injective homomorphism. It intertwines the actions when automorphisms of `T` are restrictions of automorphisms of `L`. |
| `exists_integral_coboundary` | The general vanishing theorem, explained below. |

The local field (namespace `LocalUnramified`):

| Declaration | Content |
|---|---|
| `integers F E` | The ring of integers `O_E`, defined as `integralClosure 𝒪[F] E`, a subalgebra of `E`. |
| instances | `IsFractionRing (integers F E) E`, `Module.Finite`, `Module.Free` and `IsLocalRing`. |
| `finrank_integers` | `finrank 𝒪[F] O_E = finrank F E`. |
| `isIntegral_iff_baseIntegers`, `mem_integers_iff`, `integersEquiv` | `O_E` is the Library's spectral integer ring `extensionIntegers F E`. |
| `inertia_eq_bot` | For finite Galois `E ≤ inertiaFixedField F`, the Library's inertia subgroup `inertia F E` is trivial. |
| `galoisAction F E` | The restriction homomorphism `Gal(E/F) →* (O_E ≃ₐ[𝒪[F]] O_E)`, from Mathlib's `galRestrict`. |
| `card_galois`, `galoisAction_faithful` | `|Gal(E/F)| = rank O_E`, and the action on the residue field of `O_E` is faithful. |

Corollaries:

| Declaration | Content |
|---|---|
| `GaloisCocycle.twistedValue_mul` | For a Library cocycle `ξ` on a field cover and any point `g`, `σ ↦ g⁻¹ * value ξ σ * σ(g)` satisfies the crossed-homomorphism identity. |
| `GaloisCocycle.isTrivial_of_twist` | For finite Galois `L/k`: if that twist equals `f * σ(f)⁻¹` for all `σ`, then `ξ` is trivial, with trivialization `g * f`. |
| `GaloisCocycle.isTrivial_of_integral_twist` | Over a local field: if the twisted values have integral coordinates for a smooth model `M` with connected special fibre, then `ξ` is trivial. |

`isTrivial_of_integral_twist` is the form used in KP Theorem 10.6.1: once a building argument
moves a Galois cocycle into an Iwahori subgroup, the cocycle is trivial.

## The implemented proof

**The general theorem `exists_integral_coboundary`.** Let `R` be complete for a maximal
ideal `I` with finite residue ring, and let `M` be smooth with connected special fibre over
`R ⧸ I`. Let `T ⊆ L` be a local `R`-subalgebra, finite and free over `R`. Let a finite group
`Γ` act on `L` through `act : Γ →* (L ≃ₐ[K] L)` and on `T` through
`ρ : Γ →* (T ≃ₐ[R] T)`, compatibly (`hρ`). Assume `|Γ| = rank T` and that `Γ` acts faithfully
on the residue field of `T`.

1. Each `c g` has generic coordinates in `T`, so `exists_affinePointMap_eq_of_mem` gives
   `c' g : M.group(T)` with `subalgebraPointMap (c' g) = modelPointEquiv L (c g)`.
2. `c'` is a crossed homomorphism for `ρ` (`GaloisRingCover.IsCrossed`). Apply the injective
   map `subalgebraPointMap`. Then use multiplicativity, `subalgebraPointMap_conjugate`, the
   crossed identity of `c` and `modelPointEquiv_affinePointMap`.
3. The published `integralGaloisCocycleVanishing` gives `f' : M.group(T)` with
   `c' g = f' * (conjugate (ρ g) f')⁻¹`.
4. Let `f` be the preimage of `subalgebraPointMap f'` under `modelPointEquiv L`.
   `mem_of_affinePointMap_eq` shows that its coordinates lie in `T`. Push the identity
   `c' g * conjugate (ρ g) f' = f'` through `subalgebraPointMap` and use the two
   intertwining lemmas. This gives `modelPointEquiv L (c g * σ(f)) = modelPointEquiv L f`, so
   `c g = f * σ(f)⁻¹`.

The general theorem is stated over abstract `R`, `K`, `L` and `T` for a practical reason.
Rewriting directly with the concrete local-field types made `isDefEq` time out on
`CommAlgCat.of 𝒪[F] E`.

**The local-field instance.** `localUnramifiedIntegralCocycleVanishing` applies
`exists_integral_coboundary` with `R = 𝒪[F]`, `I = 𝓂[F]`, `K = F`, `L = E`,
`T = integers F E`, `Γ = Gal(E/F)`, `act` the identity and `ρ = galoisAction F E`. The
hypotheses are supplied as follows.

- `𝒪[F] ⧸ 𝓂[F]` is the residue field `𝓀[F]`, which is finite by Mathlib. Mathlib's instance
  `IsAdicComplete 𝓂[F] 𝒪[F]` needs a uniform structure, so the proof equips `F` with its
  topological-group uniformity.
- `O_E` is finite and free over `𝒪[F]` of rank `[E : F]`. Mathlib's `IsIntegralClosure.finite`,
  `IsIntegralClosure.module_free` and `IsIntegralClosure.rank` apply, because `𝒪[F]` is a
  discrete valuation ring and `E/F` is separable.
- `O_E` is local. The Library's spectral integer ring `extensionIntegers F E` is a valuation
  subring of `E`. The published `integral_iff_mem_spectralIntegers` identifies it with the
  integral closure over the normed integer ring `baseIntegers F`. That ring has the same
  elements as `𝒪[F]` by the published `localNormedField_integer`, so integrality over the two
  rings agrees (`isIntegral_iff_baseIntegers`, via `IsIntegral.map_of_comp_eq`).
  `integersEquiv` is the resulting ring isomorphism. It is the identity on elements of `E`.
- `|Gal(E/F)| = [E : F] = rank O_E` (`card_galois`).
- Faithfulness on the residue field (`galoisAction_faithful`) needs three published facts:
  - `finiteUnramifiedMaximality` and `arithmeticUnramified_iff_residue_finrank` give residue
    degree `[k_E : k_F] = [E : F]`;
  - `isGalois_of_finite_base` makes the residue extension Galois;
  - `residueHom_surjective` makes `Gal(E/F) → Gal(k_E/k_F)` surjective.

  The two groups then have the same finite order, so this map is injective, and its kernel
  `inertia F E` is trivial (`inertia_eq_bot`). An automorphism that acts trivially on the
  residue field of `O_E` also acts trivially on the residue field of `extensionIntegers F E`,
  because `integersEquiv` matches the maximal ideals (`mem_maximalIdeal_integersEquiv_iff`).
  So it lies in `inertia F E` and equals `1`.

Integrality of coordinates is membership in `integers F E` (`mem_integralClosure_iff`).

**Corollaries.** `twistedValue_mul` follows from the published `GaloisCocycle.value_mul` and
`GaloisPoint.conjugate_mul` by group manipulation. `isTrivial_of_twist` produces the
trivialization `g * f` and applies the published `GaloisCocycle.isTrivial_iff`.
`isTrivial_of_integral_twist` combines these with the main theorem.

## Provenance

Provenance: derived. The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- Lemma 8.1.4, printed p.285 / PDF p.316: "Let G be a smooth affine o-group scheme with
  connected fibers. Then the map H1(Γ, G(O))→ H1(Γ, G(f)) is injective. In particular, if
  dim(f) ⩽ 1, then H1(Γ, G(O)) is trivial." There `Γ = Gal(K/k)`, for a maximal unramified
  extension `K` with integer ring `O` (Chapter 8 opening, printed p.283 / PDF p.314).
- Theorem 10.6.1, printed pp.397–398 / PDF pp.428–429, uses Lemma 8.1.4 to show that a
  cocycle with values in a Γ-stable Iwahori subgroup is trivial. Theorem 10.6.4,
  printed p.399 / PDF p.430, specializes it to simply connected groups, whose Iwahori
  subgroups are self-normalizing.

This module differs from the source as follows:

- It works at a finite level, with `Gal(E/F)` for a finite Galois `E` inside the inertia fixed
  field, instead of `Gal(K/k)`.
- The base is a nonarchimedean local field, so the residue field is finite and has dimension
  at most one.
- Only the special fibre is assumed connected. The generic fibre is not.
- The coefficients `M(O_E)` appear as the points of `G(E)` with integral coordinates for `M`.
- The injectivity part of Lemma 8.1.4 is not proved.

The Library definitions used are `IntegralModel`, `GaloisPoint.conjugate`,
`GaloisCocycle.value` and `Cocycle.IsTrivial`, and, for the unramified hypothesis,
`LocalGalois.Separable.inertiaFixedField`. The integer ring `integers F E` is Mathlib's
integral closure.

## Scope

This module does not prove `LocalSimplyConnectedUnramifiedCocycleVanishingStatement` or the
task target `LocalSimplyConnectedCocycleVanishingStatement`. KP Theorem 10.6.1 still needs the
building-theoretic step. That step moves a Galois cocycle of a simply connected group by a
coboundary into the integral points of an Iwahori model with connected special fibre, using
a Γ-stable chamber (KP Proposition 9.10.4) and the transitivity of `G(K)` on chambers.
`GaloisCocycle.isTrivial_of_integral_twist` then finishes the argument.
