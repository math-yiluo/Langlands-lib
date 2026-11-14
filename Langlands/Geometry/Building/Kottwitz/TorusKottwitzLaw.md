# The norm squares of the torus Kottwitz homomorphism

Helper module for the proof of `TorusKottwitzExistenceStatement`
(Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Proposition 11.1.1).
Notation: `K = UnramifiedClosure F`, `F^sep = SeparableClosure F`, `L` a finite Galois
intermediate field of `F^sep / K` over which `T` splits, `v_L = normalizedIntermediateValuation
F L`, `ord_L = IntegerValuation.orderUnits v_L`, `I = relativeInertia k K F^sep`, and
`pr : X_*(T_{F^sep}) → X_*(T)_I` the projection `inertiaProjection`.

KP define the Kottwitz map on `T(K)` by the commutative square

```
T(L) --val_L--> X_*(T)
 |N_{L/K}          | pr
 v                 v
T(K) ----κ----> X_*(T)_I
```

(printed pp. 421–422, PDF pp. 452–453). Their existence proof fixes one `L`, notes that the
top-right composite is invariant under inertia, and shows via Tate cohomology that the norm
induces an isomorphism from the coinvariants `T(L)_{Gal(L/K)}` onto `T(K)`. Uniqueness
holds because the norm is onto. This module carries out that argument for one fixed `L`,
in the equivalent form "`N_{L/K}` is onto and the composite kills `ker N_{L/K}`". The Library's `TorusNormLawAt` is
the statement that the square commutes. All declarations are derived internal
infrastructure, and `normLawValue` is just a name for the top-right composite.

## Unit orders (section `Order`)

- `not_isOfFinOrder_of_orderUnits`: a unit with nonzero order has infinite multiplicative
  order. If `a^n = 1` with `n > 0`, then `n · ord(a) = 0`.
- `exists_orderUnits_eq_one F L`: some `a ∈ L^×` has `ord_L(a) = 1`. This uses the surjectivity
  of `v_L` from `normalizedIntermediateValuation_spec'` (TorusNormValuation), applied to
  `exp(-1)`.
- `exists_not_isOfFinOrder F L`: `L^×` has a unit of infinite order.
- `orderUnits_algEquiv`: `ord_L` is `Gal(L/K)`-invariant, by
  `normalizedIntermediateValuation_algEquiv`.

## The square at one field (section `Law`)

- `normLawValue F k T L hL : Additive T(L) →+ X_*(T)_I` sends `x` to
  `pr(ext_{L→F^sep}(splitValuation(T_L, v_L)(x)))`. Here `T(L)` is the group of
  coefficient points `affinePoints T.toGrp (CommAlgCat.of k L)`, and it is identified with
  the rational points of `T_L` through `baseChangeCoeffEquiv`.
- `normLawValue_ofMul_symm`: the value on a point coming from `T_L` is exactly the
  right-hand side of `TorusNormLawAt`.
- `torusNormLawAt_iff`: `TorusNormLawAt F k T L hL κ` holds iff
  `κ(N_{L/K} x) = normLawValue(x)` for all `x ∈ T(L)`.
- `normLawValue_tmul`: on the pure evaluation `ν(w)` the value is
  `pr(ext(ord_L(w) • ν))`. This follows from `splitValuation_cocharacterPoints`
  (TorusCocharacterTower).

### Galois invariance (KP: the top composite is `Gal(L/K)`-invariant)

- `liftNormal_mem_relativeInertia`: an extension to `F^sep` of `σ ∈ Gal(L/K)` fixes `K`,
  so it lies in the inertia group `I`.
- `inertiaProjection_liftNormal`: `pr` is invariant under such an extension
  (`Representation.Coinvariants.mk_self_apply`).
- `extendGeometricCocharacters_liftNormal`: extending cocharacters from `L` to `F^sep`
  intertwines `σ` with its extension. It applies `extendGeometricCocharacters_galois` with a
  unit of infinite order.
- `normLawValue_conjugate_tmul`: by `coefficientEvaluation_galois_tmul`, `σ(ν(w)) =
  (σν)(σw)`. Here `ord_L(σw) = ord_L(w)`, and `pr ∘ ext ∘ σ = pr ∘ ext` by the two previous
  lemmas.
- `normLawValue_relativeConjugate`: `normLawValue(σx) = normLawValue(x)` for all
  `x ∈ T(L)` and `σ ∈ Gal(L/K)`. Both sides are additive in `x` and agree on pure
  evaluations, so `additive_ext_coefficientEvaluation` applies.

## Existence, uniqueness and surjectivity at one field (section `Existence`)

Here `L/K` is finite Galois and `T_L` is split.

- `relativeNorm_unramifiedClosure_surjective`: `N_{L/K} : T(L) → T(K)` is onto. This is
  `relativeNorm_surjective` (TorusNormCohomology) with `K` of dimension `≤ 1`
  (`unramifiedClosure_hasDimensionLEOne`, TorusNormValuation).
- `normLawValue_eq_zero_of_relativeNorm_eq_one`: `normLawValue` kills `ker N_{L/K}`. This
  is `invariant_eq_zero_of_relativeNorm_eq_one` (vanishing of Tate `Ĥ^{-1}`) applied with
  the Galois invariance above. The splitting over `F^sep` comes from
  `IsSplitTorus.baseChange_fieldTower`.
- `exists_torusNormLawAt`: some `κ : T(K) →* X_*(T)_I` satisfies `TorusNormLawAt` at `L`. It
  is `normLawValue` descended along the surjection `N_{L/K}` via
  `MonoidHom.liftOfRightInverse`, using the previous two lemmas.
- `eq_of_torusNormLawAt`: two homomorphisms satisfying `TorusNormLawAt` at the same `L` are
  equal, because `N_{L/K}` is onto.
- `surjective_of_torusNormLawAt`: such a homomorphism is onto. Every class in `X_*(T)_I` is
  `pr(v)` for some `v`, and `v = ext(ν)` for some `ν ∈ X_*(T_L)` because extension is
  bijective for split `T_L` (`extendGeometricCocharacters_bijective`). Choosing `a ∈ L^×`
  with `ord_L(a) = 1`, the point `N_{L/K}(ν(a))` maps to `pr(ext(ν)) = pr(v)` by
  `normLawValue_tmul`.
