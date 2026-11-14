# The algebraic core of the finite-index enlargement

Worker 33, task `e1575004-9fac-4821-9bc9-ddcb15e7cbf3` (Task 6018). This is an internal helper
module for the proof of
`Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementStatement`. It proves the algebraic
form of the theorem, `exists_hopf_enlargement`, which the final proof transports to schemes.
The definitions (`liftPoint`, `pointA`, `pointB`, `σB`, `enlargedι`) are auxiliary
constructions, derived for this proof.

## Setting

- `R` is a Henselian discrete valuation ring with algebraically closed residue field, `K` its
  fraction field, and `ϖ` a uniformiser.
- `A` is a smooth commutative Hopf algebra over `R`, `P` a group, and
  `ev : P →* WithConv (A →ₐ[R] K)` a monoid homomorphism into the convolution monoid. We write
  `ev x a` for the value at `a`.
- `U ≤ V ≤ P` are subgroups. `U` satisfies:
  - `hU`: `x ∈ U` iff all values `ev x a` lie in `R`;
  - `hsurj`: every integral point `σ : A →ₐ[R] R` gives `ofId ∘ σ = ev u` for some `u`.
- `T` is a finite set with `V ⊆ ⋃_{r ∈ T} r U`.

## Integral points

- `liftPoint f hf` turns `f : C →ₐ[R] K` with all values in `R` into `C →ₐ[R] R`, through
  `AlgEquiv.ofInjective` of `R → K`. `algebraMap_liftPoint` and `ofId_comp_liftPoint` recover
  `f`. `eq_of_ofId_comp_eq`: integral points with the same image in `K` are equal.
- `mem_range_of_isIntUnit_mul`: if `a` is a unit value and `a b ∈ R`, then `b ∈ R`.

## Localizations

- `awayMap_bijective_of_forall`: for an injective ring map `φ : S → T` and `r : S`, the map
  `S[1/r] → T[1/φ r]` is bijective if every `a : T` satisfies `φ b = φ(r) ^ n a` for some `n`
  and `b` (Mathlib's `Localization.awayMap_injective_iff` and `awayMap_surjective_iff`).
- `smooth_away_of_bijective`: if `T` is smooth over `R` and `S[1/r] → T[1/φ r]` is bijective,
  then `S[1/r]` is smooth over `R`. The target is a localization of a smooth algebra.
- `exists_eq_smul_of_mem_map`: an element of `𝔪_R C` is `ϖ c'`.

## Points of a Hopf algebra `B`

Let `B` be a commutative Hopf algebra over `R` with a bialgebra map `ι : B →ₐc[R] A` such that
`hB`: `a ∈ range ι` iff `ev x a ∈ R` for all `x ∈ V`.

- `pointA u : A →ₐ[R] R` is the integral point given by `u ∈ U` (via `hU`).
- `pointB z : B →ₐ[R] R` is the integral point `b ↦ ev z (ι b)` given by `z ∈ V` (via `hB`).
- `σB : V →* WithConv (B →ₐ[R] R)`, `z ↦ pointB z`, is a monoid homomorphism. The unit goes to
  the counit, and products go to convolution products, because `ι` is a bialgebra map
  (`AlgHom.comp_convMul_distrib`, `AlgHom.convMul_comp_bialgHom_distrib`).
- `ev_ι_pointTrans`: `ev x (ι (pointTrans (pointB z) b)) = ev (x * z) (ι b)`
  (`comp_pointTrans` of module `PointTranslation`).
- `pointB_eq_comp`: for `u ∈ U`, `pointB u = pointA u ∘ ι`.

## Main section

Assume moreover that `ι` is injective. The results use an element `b₀ : B` with
`ε(b₀)` a unit and `hsmall`: `ev x (ι b₀)` is small for every `x ∈ V \ U`.

- `exists_ι_eq_pow_mul`: every `a : A` has `ϖ ^ n a ∈ range ι` (bounded denominators on `V`,
  `exists_bound`).
- `exists_ι_eq_pow_mul_of_small`: if `e : B` has small values on `V \ U`, then every
  `a : A` has `ι e ^ n a ∈ range ι`. Take `n = N + 1` with `N` a bound for `a`. On `U`, both
  factors are integral; on `V \ U` use `isIntSmall_mul_pow`.
- `isIntSmall_pointTrans`: translating such an `e` by `pointB u`, `u ∈ U`, preserves smallness
  on `V \ U`, because `x u ∉ U` when `x ∉ U`.
- `exists_eq_smul_of_forall_pointA`: the points `pointA u` detect divisibility by `ϖ` in `A`.
  This combines `mem_map_maximalIdeal_of_forall` (module `IntegralPoints`) with `hsurj`.
- `exists_eq_smul_of_forall_pointB`: the points `pointB z`, `z ∈ V`, detect divisibility by `ϖ`
  in `B`. If all `pointB z b` lie in `𝔪`, then:
  1. the points `pointA u` give `ι b = ϖ a'`;
  2. `a'` is integral on `V`, since `ϖ ev z a' = ev z (ι b)` is divisible by `ϖ` in `R`;
  3. so `a' = ι b'` by `hB`, and `b = ϖ b'` by injectivity of `ι`.
- `span_cover_B` and `span_cover_A`: `ϖ` together with the translates of `b₀` by the points of
  `V` generates the unit ideal of `B`. Likewise `ϖ` with the translates of `ι b₀` by the points
  of `U` generates the unit ideal of `A`. Both follow from the covering lemma
  `span_insert_pointTrans_eq_top` (module `Cover`).

### Smoothness (`smooth_of_core`)

`B` is smooth over `R`. By `RingHom.Smooth.ofLocalizationSpanTarget` it suffices to check that
`B[1/s]` is smooth for every `s` in the generating set of `span_cover_B`:

- for `s = ϖ`, `B[1/ϖ] → A[1/ϖ]` is bijective by `exists_ι_eq_pow_mul`, so `B[1/ϖ]` is smooth;
- for `s = b₀`, `B[1/b₀] → A[1/ι b₀]` is bijective by `exists_ι_eq_pow_mul_of_small` and
  `hsmall`, so `B[1/b₀]` is smooth;
- for a translate `s = pointTrans (σB z) b₀`, the automorphism `transEquiv (σB) z` of `B`
  (module `PointTranslation`) sends `b₀` to `s`. It induces `B[1/b₀] ≅ B[1/s]`.

### Generic fibre (`baseChange_bijective_of_core`)

`K ⊗[R] B → K ⊗[R] A` is bijective.

- Injectivity: `K` is flat over `R` and `ι` is injective.
- Surjectivity: by `exists_ι_eq_pow_mul`, `c ⊗ a = c ϖ⁻ⁿ ⊗ ι b` with `ι b = ϖ ^ n a`.

`tensorMap_apply_eq_lTensor` identifies the algebra map with `lTensor`.

### Open immersion (`isOpenImmersion_of_core`)

`Spec A → Spec B` is an open immersion. Apply `isOpenImmersion_specMap_of_away_bijective`
(module `OpenImmersionCriterion`, by Worker 260) to the family indexed by `Option U`: `ϖ` and the
translates `pointTrans (pointB u) b₀` for `u ∈ U`.

- Their images generate the unit ideal of `A`. They contain the generators of `span_cover_A`,
  because `ι (pointTrans (pointB u) b₀) = pointTrans (pointA u) (ι b₀)`; this is
  `pointB_eq_comp` with `map_pointTrans`.
- Each localization map is bijective, by `exists_ι_eq_pow_mul`, or by
  `exists_ι_eq_pow_mul_of_small` together with `isIntSmall_pointTrans`.

### Points (`mem_of_forall_ev_ι`)

If `ev x (ι b) ∈ R` for every `b : B`, then `x ∈ V`. Let `τ = liftPoint (ev x ∘ ι)`, an
integral point of `B`. Mapping `span_cover_B` along `τ` shows that the values of `τ` on the
generators generate `R`. Since `R` is local, one value is a unit. It cannot be `τ ϖ = ϖ`, so it
is the value at some translate. By `ev_ι_pointTrans` that value is `ev (x z) (ι b₀)`, a unit
value, for some `z ∈ V`.

Then `x z ∈ U`. For each `a : A`, write `ι b = ι b₀ ^ n a` (`exists_ι_eq_pow_mul_of_small`).
Then `ev (x z) (ι b₀) ^ n · ev (x z) a = ev x (ι (pointTrans (pointB z) b))` is integral, and
`mem_range_of_isIntUnit_mul` gives `ev (x z) a ∈ R`. Hence `x z ∈ U` by `hU`, and
`x = (x z) z⁻¹ ∈ V`.

`core_of_hopf` bundles the four results. The converse direction of the points statement is
`ev_ι_mem`.

## Assembly

`enlargedι hfin` is the bialgebra inclusion `SubHopf.valBialgHom` of `enlarged ev V` with the
Hopf structure `enlargedHopfAlgebra` (module `Enlarged`).

`exists_hopf_enlargement` (**algebraic core**): under the standing hypotheses, with `U ≤ V`
and `U.subgroupOf V` normal of finite index, there are a commutative Hopf algebra
`B : CommHopfAlgCat R` and a bialgebra map `ι : B →ₐc[R] A` such that:

- `B` is smooth over `R`;
- `Algebra.TensorProduct.map (AlgHom.id K K) ι` is bijective;
- `Spec.map ι` is an open immersion;
- for every `x : P`, all `ev x (ι b)` lie in `R` iff `x ∈ V`.

Proof: the coset lemmas of module `Separating` give the conjugation property, a uniform
exponent `n + 1` with `x ^ (n + 1) ∈ U` on `V`, and finite coset representatives (filtered to
lie in `V` for `HasReps`). `exists_separating` gives `e`: integral on `V`, a unit at `1`, and
small on `V \ U`. Take `B = enlarged ev V` with `ι = enlargedι`; it is injective, and `hB` is
`mem_enlarged`. Take `b₀ = e`; its counit is a unit because `ev 1 e = ε(e)` is a unit value.
Then apply `core_of_hopf`.

## Provenance

This is the algebraic content of Kaletha–Prasad Proposition A.7.1(1)–(4), finite-index case,
in the coordinate-ring formulation used for this formalization. The proofs are derived. They
do not follow the gluing argument of the source.
