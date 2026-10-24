# The Herbrand quotient of the integral ideles

Author: Worker 226.

The main theorem is

`IntegralIdeleHerbrand.cyclicIntegralIdeleHerbrand_of :
  ArchimedeanCompletionHerbrand.{v} → CyclicIntegralIdeleHerbrand.{u, v}`.

Both propositions are stated in `Langlands.ClassField.Global.IntegralIdeleHerbrandStatement`.
So `h(J∞) = D∞`, assuming the archimedean local input. This module does not prove that
input; Worker 269's separate candidate `Langlands.ClassField.Global.ArchimedeanLocalHerbrand`
(`hasHerbrandQuotient_infiniteLocalRepresentation`) supplies it.
The common-universe form is `IntegralIdeleHerbrand.integralIdeleHerbrand`. For
`F E : Type u` with `[IsGalois F E]` and `[IsCyclic (E ≃ₐ[F] E)]`, it takes the per-place
archimedean hypothesis and concludes that `H¹(J∞)` and `H²(J∞)` are finite with
`Nat.card H² = archimedeanHerbrandFactor F E * Nat.card H¹`.

## The local factors

Write `G = Gal(E/F)`. In the common-universe sections the module assumes `[Normal F E]`, and
`[IsGalois F E]` where needed.

- Finite places. `unitCoordinate w : integralIdeles E →* localUnits w` is the coordinate at
  the finite place `w`, which is a valuation unit. `integralLocalProjection w v`, for
  `[w.asIdeal.LiesOver v.asIdeal]`, is this coordinate as a morphism from `J∞` (restricted
  along `decompositionHom v w`) to `localUnitsRepresentation v w`. Equivariance is the
  Library's `ideleCoordinate_relativeIdeleAut_decompositionHom`.
  `integralSemilocalProjection w v : J∞ ⟶ Coind(U_w)` is its adjoint
  `x ↦ (g ↦ (g • x)_w)` (Mathlib's `Rep.resCoindToHom`). Its composite with the Library's
  `coindLocalUnitsInclusion` is the Library's `ideleSemilocalProjection` of the underlying
  idele (`coindLocalUnitsInclusion_integralSemilocalProjection`).
- The index type `PlaceIndex F E = HeightOneSpectrum (𝓞 F) ⊕ infinitePlaceOrbits F E`.
  For a finite place `v` of `F`, `finitePlace v` is the Library's chosen place
  `(placeAbove E v).1` above it. For an orbit `O` of infinite places, `infinitePlace O` is
  the representative `O.out`.
- `factor i` is `Rep.coind (decompositionHom v (finitePlace v)) (localUnitsRepresentation …)`
  for `i = inl v`. For `i = inr O` it is
  `Rep.coind (stabilizer (infinitePlace O)).subtype (infiniteLocalRepresentation F …)`.
  `projection i : J∞ ⟶ factor i` is `integralSemilocalProjection` for finite indices and the
  Library's `infiniteSemilocalProjection` (after `integralIdeleInclusion`) for infinite ones.

## The product decomposition

- `eq_zero_of_projection_eq_zero`: an integral idele with all projections trivial is trivial.
  Its infinite part is `1`: every infinite place `w` is `infinitePlaceEquiv g (O.out)` for its
  orbit `O` (`infinitePlace_mem_orbit`), and the Library's
  `ideleInfiniteCoordinate_eq_of_infiniteSemilocalProjection_eq` applies. Every finite
  coordinate is `1` by `ideleCoordinate_eq_of_ideleSemilocalProjection_eq` at the place below.
- `exists_projection_eq`: for every family `b i ∈ factor i` there is an integral idele with
  these projections. For each finite `v`, take the Library's semilocal section of `b (inl v)`,
  viewed in `Coind(E_wˣ)`. For each orbit `O`, take the infinite semilocal section of
  `b (inr O)`. The glued idele has, at a finite place `w`, the coordinate of the section for
  `placeBelow F w`, and, at an infinite place `w`, the coordinate of the section for the orbit
  of `w`. It is built as `ideleOfCoordinates · ideleOfInfiniteCoordinates`. Its finite
  coordinates are valuation units (`ideleCoordinate_mem_localUnits_of_ideleSemilocalProjection`),
  so it lies in `J∞`. Its projections agree with those of the sections, because the
  coordinates of `g • x` at `w` only involve coordinates of `x` over the same place of `F`
  (`ideleCoordinate_relativeIdeleAut_eq`), resp. in the same orbit
  (`ideleInfiniteCoordinate_relativeIdeleAut_eq_iff`, `quotient_mk_infinitePlaceEquiv`). The
  section-then-projection identities are the Library's
  `ideleSemilocalProjection_ideleSemilocalSection` and
  `infiniteSemilocalProjection_infiniteSemilocalSection`.
- `cohomologyEquiv n hn`: `Langlands.Cohomology.ProductDecomposition.productEquiv` then gives
  `Hⁿ(G, J∞) ≃ ∏_i Hⁿ(G, factor i)` for `n = 1, 2`.

## Local cohomology and counting

- `factorEquivFinite`, `factorEquivInfinite`: Shapiro's lemma (`Shapiro.shapiroIsoOf`, along
  the injective `decompositionHom` resp. the subgroup inclusion) identifies `Hⁿ(G, factor i)`
  with `Hⁿ(Gal(E_w/F_v), U_w)` resp. `Hⁿ(D_w, E_wˣ)`. `hasHerbrandQuotient_of_equiv` transports
  Herbrand quotients along such equivalences between different groups.
- `hasHerbrandQuotient_factor_inl`: for cyclic `G` the local Galois group is cyclic
  (`isCyclic_of_injective` along `decompositionHom`), so the finite factors have Herbrand
  quotient `1` by `LocalUnitHerbrand.hasHerbrandQuotient_localUnits`.
- `subsingleton_factor_inl`: at an unramified `v` both groups are trivial by
  `unramifiedCompletionUnitVanishing`.
- `finite_ramifiedPlaces`: only finitely many `v` have ramified chosen places (the Library's
  `finite_setOf_ramificationIdx_ne_one` and `placeBelow_eq`).
- `integralIdeleHerbrand`: let `S` be the finite set of ramified finite indices together
  with all infinite orbits. Outside `S` all factors have trivial `H¹` and `H²`. So
  `Nat.card Hⁿ(J∞) = ∏_{i ∈ S} Nat.card Hⁿ(factor i)` and these groups are finite
  (`natCard_pi_eq_prod`, `finite_pi`). At each `i ∈ S`, `|H²| = q_i · |H¹|` with `q_i = 1`
  at finite indices and `q_i = |D_w|` at infinite ones; the latter is the archimedean
  hypothesis. Multiplying gives `|H²(J∞)| = (∏_O |D_{O.out}|) · |H¹(J∞)|`. The product is
  `archimedeanHerbrandFactor F E` by Worker 343's `archimedeanHerbrandFactor_eq_prod`.

## Independent universes

For `F : Type u` and `E : Type v`, replace `F` by its image `F₀ = (⊥ : IntermediateField F E)`
in `E`, using Worker 343's `baseImageAutEquiv F E : Gal(E/F) ≃* Gal(E/F₀)`:

- `integralIdeleCohomologyBaseImageIso`: `groupCohomology.mapIso` along `baseImageAutEquiv`
  and the identity of `J∞`. The actions agree definitionally.
- `natCard_stabilizer_baseImage` and `archimedeanHerbrandFactor_baseImage`: the two groups act
  in the same way on the infinite places, so the orbit types correspond (`Quotient.congr`)
  and the stabilizer orders agree.
- `cyclicIntegralIdeleHerbrand_of` applies `integralIdeleHerbrand` to `F₀` and transports
  finiteness and cardinalities back.

## Provenance

The argument is that of E. Artin and J. Tate, *Class Field Theory* (2009), source
`artin-tate-2009-class-field-theory`, Chapter V §§2–3, printed pp.12–13 (PDF pp.21–22). The
semilocal isomorphism is used there as `Hʳ(G, ∏_{P|p} U_P) ≈ Hʳ(G_p, U_p)`. Cohomology of
the product is used as `Hʳ(U) ≈ ∏_p Hʳ(G_p, U_p)`. Only finitely many places ramify, and the
local values are `h(U_p) = 1`, `h1(G_p, K_pˣ) = 1`, `h2(G_p, K_pˣ) = n_p` at the
archimedean places. See also J. S. Milne, *Class Field Theory* v4.03 (2020), source
`milne-2020-class-field-theory`, Chapter VII Proposition 2.7, printed p.206 (PDF p.215). The
explicit gluing of sections, the choice of index type and representatives, and the universe
transport are internal. The local inputs are this project's unconditional local-unit
theorems and the archimedean hypothesis. Nothing about `C_E` or the ideal class group is
used.
