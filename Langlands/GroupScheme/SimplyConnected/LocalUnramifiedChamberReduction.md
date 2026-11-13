# The integral twist from a Galois-stable chamber

This module proves that the building input
`LocalSimplyConnectedUnramifiedChamberStatement` (module
`LocalUnramifiedChamberStatement`) implies the interface statement
`LocalSimplyConnectedUnramifiedIntegralTwistStatement` (module
`LocalUnramifiedIntegralTwistStatement`). It does not prove the chamber
statement.

Throughout, `F` is a nonarchimedean local field, `L = inertiaFixedField F` is
its maximal unramified extension inside the separable closure,
`Γ = Gal(L/F)` (`L ≃ₐ[F] L`), and `G(L) = rationalPoints (baseChanged F L G)`
with Galois action `σ(g) = rationalConjugate F L G σ g`.
`Φ = baseChangeCoeffEquiv F L G` is the group isomorphism from `G(L)` to the
coefficient points `G.affinePoints (CommAlgCat.of F L)`.

## Statements

- `LocalSimplyConnectedUnramifiedChamberReductionStatement : Prop` is the
  implication
  `LocalSimplyConnectedUnramifiedChamberStatement.{u} →
  LocalSimplyConnectedUnramifiedIntegralTwistStatement.{u}`.
  The theorem `localSimplyConnectedUnramifiedChamberReduction` proves it.

Three auxiliary results are proved on the way.

- `isIntegral_of_mem_fixedFieldIntegers`: every element of
  `fixedFieldIntegers F`, the valuation ring of `L`, is integral over `𝒪[F]`
  as an element of `L`.
- `IntegralModel.hasIntegralCoordinates_of_mem_baseChangeUnramified`: let
  `M : IntegralModel 𝒪[F] F G` and let `p` be a coefficient point of `G` over
  `L`. If `Φ⁻¹ p` lies in `M.baseChangeUnramified.integralPoints` (the image in
  `G(L)` of the integral points of the base change of `M` to
  `fixedFieldIntegers F`), then `M.HasIntegralCoordinates L p`: every regular
  function of `M` takes a value at `p` that is integral over `𝒪[F]`.
- `image_smul_eq_self_of_twisted_stable`: a statement about any group `H`
  acting on a type `X`. Let `f : X → X` and `s : H → H` satisfy
  `f (g • z) = s g • f z`. Let `Y₀, Y ⊆ X` and `g, c ∈ H` with
  `f '' Y₀ = Y₀`, `(g • ·) '' Y₀ = Y` and `(fun y => c • f y) '' Y = Y`. Then
  `((g⁻¹ * c * s g) • ·) '' Y₀ = Y₀`.

## Proof

*Integrality over `𝒪[F]`.* By `fixedFieldIntegers_eq`, `fixedFieldIntegers F`
equals `extensionIntegers F L`, the elements of spectral norm at most one.
`spectral_integral` shows that such elements are integral over
`baseIntegers F`. `LocalUnramified.isIntegral_iff_baseIntegers` identifies
integrality over `baseIntegers F` with integrality over `𝒪[F]`.

*Integral coordinates.* The proof introduces the `𝒪[F]`-algebra structure on
`fixedFieldIntegers F` and the scalar tower `𝒪[F] → fixedFieldIntegers F → L`
from `Valuation.HasExtension`. By `mem_coefficientIntegralPoints_iff`, `p` is a
coefficient integral point of `M.baseChangeUnramified`, which is by definition
`M.baseChange (fixedFieldIntegers F) L`. By
`mem_baseChange_coefficientIntegralPoints_iff_genericCoordinates`, every
generic coordinate of `p` lies in the image of `fixedFieldIntegers F` in `L`.
The first auxiliary result makes each such value integral over `𝒪[F]`.

*Twisted stability.* For every `y`,
`(g⁻¹ * c * s g) • f y = g⁻¹ • (c • f (g • y))`, by the intertwining property
of `f`. Hence the image of `Y₀ = f '' Y₀` under translation by
`g⁻¹ * c * s g` is the image under `g⁻¹ •` of the twisted image of
`(g • ·) '' Y₀ = Y`. That twisted image is `Y`, and `g⁻¹ • Y = Y₀`.

*The reduction.* Assume the chamber statement and fix `F` and a simply
connected `G`. The chamber statement gives building data `C`, semilinear
Galois data `D`, a model `M` and a chamber `Y₀`. The model `M` is smooth with
connected special fibre, and these are the first two conclusions. Let
`E/F` be finite Galois with an `F`-embedding into `L` (given as a scalar
tower `F → E → L`), and let `c : Gal(E/F) → G(E)` be a crossed homomorphism.

1. *Inflation.* Put
   `c' σ = Φ⁻¹ (GaloisPoint.relativeExtend F E L G (c (σ.restrictNormal E)))`
   for `σ ∈ Γ`. Restriction `σ ↦ σ.restrictNormal E` is multiplicative
   (`AlgEquiv.restrictNormalHom`), relative extension is a group
   homomorphism, and `GaloisPoint.relativeExtend_conjugate` together with
   `baseChangeCoeffEquiv_rationalConjugate` turns the conjugation on `G(E)`
   into the rational conjugation on `G(L)`. So `c'` satisfies
   `c' (σ * τ) = c' σ * σ(c' τ)`.
2. *Finite level.* From `c (1 * 1) = c 1 * c 1` one gets `c 1 = 1`. Let `E'`
   be the field range of the `F`-algebra map `E → L`; it is finite-dimensional
   over `F` because it is isomorphic to `E` (`AlgHom.equivFieldRange`). If `σ`
   fixes `E'` pointwise, then `σ.restrictNormal E = 1` by
   `AlgEquiv.restrictNormal_commutes` and injectivity of `E → L`, so
   `c' σ = 1`.
3. *Twisted chamber.* The last clause of the chamber statement, applied to
   `c'` and `E'`, gives a chamber `Y` with
   `(fun y => c' σ • D.action σ y) '' Y = Y` for every `σ`. Transitivity on
   chambers gives `g ∈ G(L)` with `(g • ·) '' Y₀ = Y`. Put `h = Φ g`.
4. *Integrality.* Fix `σ ∈ Γ`. Apply `image_smul_eq_self_of_twisted_stable`
   with `f = D.action σ`, `s = σ(·)`, whose intertwining property is
   `D.action_smul σ`, and with the `Γ`-stability `D.action σ '' Y₀ = Y₀` of
   `Y₀`. It shows that `k = g⁻¹ * c' σ * σ(g)` stabilizes `Y₀`. By the
   stabilizer clause of the chamber statement, `k` lies in
   `M.baseChangeUnramified.integralPoints`, so `Φ k` has integral coordinates
   for `M` by the second auxiliary result.
5. *Rewriting.* `Φ` is multiplicative, `Φ (g⁻¹) = (Φ g)⁻¹`,
   `Φ (c' σ) = relativeExtend F E L G (c (σ.restrictNormal E))`, and
   `Φ (σ(g)) = GaloisPoint.conjugate F L G σ (Φ g)`
   (`baseChangeCoeffEquiv_rationalConjugate`). Hence
   `Φ k = h⁻¹ * relativeExtend F E L G (c (σ.restrictNormal E)) * GaloisPoint.conjugate F L G σ h`,
   which is the required conclusion.

The final rewriting step needs a slow definitional unfolding between the
instance terms elaborated in the interface statement and the local ones.
The theorem therefore raises `maxHeartbeats` to `800000`.

## Provenance

The reduction is internal. It is the formal counterpart of the step in the
proof of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Theorem 10.6.1 (printed pp. 397–398), where a chamber stable under the
twisted action is moved to the `Γ`-stable chamber and the twisted cocycle
then takes values in its stabilizer, the Iwahori subgroup. The source
material for the chamber statement itself is recorded in
`LocalUnramifiedChamberStatement.md`. The inflation of a finite-level cocycle
to `Gal(L/F)`, the finiteness bookkeeping, and the translation between
rational points, coefficient points and integral coordinates are specific to
the Library's formulation.
