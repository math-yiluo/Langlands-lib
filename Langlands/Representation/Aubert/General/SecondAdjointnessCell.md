# Second adjointness from open-cell functions

Module `Langlands.Representation.Aubert.General.SecondAdjointnessCell`, namespace
`Langlands.Aubert.General`.

## Source and purpose

Renard 2026, VI.9.6 (printed p.202, PDF p.208), deduces second adjointness (VI.9.6.1),
`i ⊣ r̄`, from the chain (VI.9.6.3)

`Hom_G(V, (i τ)~) ≃ Hom_G(V, i(τ~)) ≃ Hom_M(r V, τ~) ≃ Hom_M(τ, (r V)~) ≃ Hom_M(τ, r̄(V~))`.

The text says the resulting bijection is natural and that second adjointness follows. In
this formalization the step from the chain to an adjunction is
`SmoothRep.nonempty_adjunction_of_frobeniusChain_unit` (module
`Category/ChainUnitAdjunction`). Its one extra condition is per object: the unit of the
chain at `τ`, a morphism `τ ⟶ r̄((i τ)~~)`, factors through `r̄` of bidual evaluation
`ι : i τ ⟶ (i τ)~~`. Renard does not state this condition. This module proves it from an
explicit computation with open-cell functions, which is the usual argument of Casselman
and Bernstein for the second adjointness. Both the condition and the computation are
internal to this formalization. This module proves no statement for represented
parabolics. The generic theorem below takes the inputs `C`, `Ψ` and the exactness of `r̄`
as hypotheses.

## Setting

- `G` is a locally compact nonarchimedean topological group, in universe `uG`.
- `h : IsSemidirectDecomposition P M U`: `P = M ⋉ U` as subgroups of `G`. `hU` says `U`
  is closed, and `hproj` says the projection `P → M` is continuous.
- `O` is a closed subgroup of `G` normalized by `M` (`hO`, `hMO`). `hPO` says
  `P ∩ O = 1`.
- `i = normalizedInductionFunctor h hU`, normalized induction from `M` to `G`.
  `r = jacquetFunctor h hU` is the normalized Jacquet functor along `U`.
  `r̄ = normalizedJacquetFunctor O M hO hMO` is the normalized Jacquet functor along `O`.
  `D` is the smooth contragredient, written `V ↦ V~`.
- `inducingRepresentation h hU A` is `p ↦ δ_P^{1/2}(p) A(p)` on `P`. An element of `i A`
  is evaluated with `Induction.eval`.

## Declarations

### Open-cell functions (section `Cell`)

- `cellFunction h hU A K hK t ht`: for a compact open subgroup `K` and a vector `t ∈ A`
  fixed by `P ∩ K` under the inducing representation, this is the function in `i A`
  supported on `P K` with `f_{t,K}(p k) = δ_P^{1/2}(p) A(p) t`. It is the Library's
  `Induction.compactDoubleCosetSection` at the double coset of `1`.
- `cellWeight h hU K y`: the weight `δ_P^{1/2}(p)^2` of the cell, for a chosen
  decomposition `y = p k` with `p ∈ P` and `k ∈ K`, and `0` off `P K`.
- `cellConstant h hU S μ K`: the integral over `S` against `μ` of the cell weight.
- `cellFunction_apply`, `cellFunction_eq_zero`, `cellFunction_mem_fixedVectors`,
  `cellFunction_apply_one`: the value at `p k` is `δ_P^{1/2}(p) A(p) t`. The function
  vanishes off `P K`, is fixed by `K`, and takes the value `t` at `1`.
- `smoothDualPairing_smoothContragredient_apply_apply`: `⟨m ψ, m t⟩ = ⟨ψ, t⟩`.
- `eval_hom_of_mem_fixedVectors`: if `x` is `K`-fixed and `φ` maps into `i B`, then
  `(φ x)(k) = (φ x)(1)` for `k ∈ K`.
- `smoothDualPairing_eval_cellFunction`: if `F ∈ i(A~)` and `F(k) = F(1)` on `K`, then
  `⟨F(y), f_{t,K}(y)⟩ = w_K(y) ⟨F(1), t⟩`.
- `smoothDualPairing_cellFunction`: let `C : i.op ⋙ D ≅ D ⋙ i` satisfy
  `IsNaturalIntegralDuality h hU S μ C`, that is `⟨ℓ, f⟩ = ∫_S ⟨(C ℓ)(k), f(k)⟩ dμ(k)`.
  Then for a `K`-fixed `ℓ ∈ (i A)~`, `⟨ℓ, f_{t,K}⟩ = c_K ⟨(C ℓ)(1), t⟩`, where
  `c_K = cellConstant h hU S μ K`.

### The coset relation (section `Coset`)

Assume `hPO` and `K ≤ K₀`, both compact open and both factoring as `k = p o` with `p ∈ P`
and `o ∈ O ∩ K` (respectively `O ∩ K₀`).

- `eval_cellFunction_eq_sum`: pointwise,
  `f_{t,K₀}(y) = Σ_{q ∈ (K₀ ∩ O)/(K ∩ O)} f_{t,K}(y q)`.
- `cellFunction_eq_sum`: the same identity in `i A`, `f_{t,K₀} = Σ_q q · f_{t,K}`.
- `exists_mk_cellFunction_eq_smul`: in the Jacquet module along `O`,
  `[f_{t,K₀}] = N [f_{t,K}]` for some natural number `N` (the index
  `[K₀ ∩ O : K ∩ O]`).

### Lifts and the factorization (section `Lift`)

- `eq_zero_of_forall_fixed_smoothDualPairing`: on a compact open level `K`, a `K`-fixed
  vector that pairs to zero with every `K`-fixed smooth functional is zero.
- `exists_openSubgroup_forall_mem_fixedVectors`: every `t ∈ A` is fixed by `P ∩ K`, under
  the inducing representation, for all `K` below some open subgroup.
- `hom_mem_fixedVectors`, `hom_injective_of_iso`: intertwiners preserve fixed vectors, and
  the underlying map of an isomorphism is injective.
- `exists_comp_eq_of_injective`: if `φ : Y ⟶ Z` is injective and every value of
  `ζ : X ⟶ Z` lies in the image of `φ`, then `ζ = η ≫ φ` for some `η`.
- `exists_eq_of_cellRelations`: a scalar normalization lemma in linear algebra. Let
  classes `e_K` be indexed by good levels `K`, cofinal in a meet-semilattice. Suppose
  `e_{K₀} = N e_K` for some natural `N` when `K ≤ K₀`, and that for each `x`,
  `Φ(e_K, x) = c_K ξ(x)` for all small good `K`. If `c_K = 0` at a good `K` forces
  `ξ = 0`, then `ξ = Φ(b, ·)` for some `b`.
- `exists_mul_of_isIwahoriContraction`: an Iwahori contraction
  `K = (K ∩ U)(K ∩ M)(K ∩ O)` writes each `k ∈ K` as `p o` with `p ∈ P` and `o ∈ K ∩ O`.
- `exists_forall_smoothDualPairing_cellFunction`: the key computation. Let
  `Ψ : r̄(V~) ≅ (r V)~` satisfy Worker 937's `IsStableLiftDuality O M U … g Ψ`, and let
  `ξ` be the functional `[v] ↦ ⟨(C v)(1), t⟩` on `r((i A)~)`. For each class `x`, and for
  every small compact open `K` with Iwahori contractions for `g` in the order `(O, M, U)`
  and for `g⁻¹` in the order `(U, M, O)`,
  `⟨Ψ(r̄(ι)[f_{t,K}]), x⟩ = c_K ξ(x)`. Proof: the stable-lift property gives a `K`-fixed
  lift `v` of `x` with `⟨Ψ[Λ], x⟩ = Λ(v)` for every `K`-fixed `Λ ∈ (i A)~~`. Take
  `Λ = ι f_{t,K}` and apply `smoothDualPairing_cellFunction`.
- `exists_hom_map_bidualHom_eq`: with in addition `hproj`, `hPO` and
  `hB : HasOppositeIwahoriContractionBasis O M U g`, the functional `ξ` equals
  `Ψ(r̄(ι) b)` for some `b ∈ r̄(i A)`. Proof: apply `exists_eq_of_cellRelations`. The good
  levels are the compact open `K` with both contractions and with `t` fixed by `P ∩ K`.
  `hB` makes them cofinal. The coset relation and the key computation supply the two
  relations. If `c_K = 0`, then `f_{t,K}` pairs to zero with every `K`-fixed functional,
  by `smoothDualPairing_cellFunction`, so `f_{t,K} = 0`, so `t = f_{t,K}(1) = 0` and
  `ξ = 0`.
- `nonempty_secondAdjunction_of_stableLift`: the generic form of (VI.9.6.1). The
  hypotheses are:
  - `hδ : IsUnimodularModulus U hU`, `hproj`, `hPO`, `hO`, `hMO`;
  - `hR`: `r̄` preserves short exact sequences;
  - `C` with `hC : IsNaturalIntegralDuality h hU S μ C`;
  - `g` with `hB : HasOppositeIwahoriContractionBasis O M U g`;
  - `Ψ` with `hΨ : IsStableLiftDuality O M U … g Ψ`.

  The conclusion is `Nonempty (i ⊣ r̄)` at universes `.{uG, max uG uV}`. Proof: apply
  `SmoothRep.nonempty_adjunction_of_frobeniusChain_unit` with Frobenius reciprocity
  `firstAdjointnessAdjunction h hU hδ` (Library) and the cofinality of compact open
  subgroups. Fix `τ`. The morphism `r̄(ι) ≫ Ψ` is injective, because `Ψ` is an
  isomorphism, `ι` is injective and `r̄` is exact. The chain-side morphism
  `bidualHom τ ≫ D(F.counit) ≫ D(r(C τ))` sends `t` to the functional
  `[v] ↦ ⟨(C v)(1), t⟩` (definitional, `fun v => rfl`). By `exists_hom_map_bidualHom_eq`
  that functional lies in the image of `r̄(ι) ≫ Ψ`, so `exists_comp_eq_of_injective` gives
  `η₀` with `η₀ ≫ r̄(ι) ≫ Ψ.hom` equal to the chain morphism. Composing with `Ψ.inv` gives
  the required factorization.

## Axioms

`nonempty_secondAdjunction_of_stableLift` depends only on `propext`, `Classical.choice`
and `Quot.sound`.
