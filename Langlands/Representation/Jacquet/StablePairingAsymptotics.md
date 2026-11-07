# Asymptotics of the stable pairing (abstract Theorem I.4.1)

Author: Worker 249.

This module proves the asymptotic formula of Casselman's canonical pairing in the
abstract framework of `Langlands.Representation.Jacquet.StablePairingProof`. The
source statement is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), Théorème I.4.1,
p. 245 (`waldspurger-2003-plancherel`), which Waldspurger attributes to Casselman
([C, Proposition 4.2.3 et Théorème 4.2.4]):

> Il existe un produit bilinéaire non dégénéré et invariant par `M` sur
> `V_P × (V̌_P̄)`, noté `⟨·,·⟩_P`, de sorte que pour tout `(v, v̌) ∈ V × V̌`, il
> existe `ε > 0` tel que, pour tout `a ∈ A_M` vérifiant `|α(a)|_F < ε` pour tout
> `α ∈ Δ(P)`, on ait
> `⟨π_P(a) j_P(v), ǰ_P̄(v̌)⟩_P = δ_P(a)^{-1/2} ⟨π(a)v, v̌⟩`.

Here `π_P` is the normalized Jacquet module of I.3:
`π_P(m) j_P(v) = δ_P(m)^{-1/2} j_P(π(m)v)`.

The abstraction, the hypotheses and the proof route are internal to this project. The
group-theoretic input is the Library structure `StablePairingData` and the
representation-theoretic input is its `Admits` predicate. Nothing in this module
constructs these data for an actual parabolic subgroup of an actual reductive group.
It also does not prove that the elements of `A_M` with `|α(a)|_F < ε` for all
`α ∈ Δ(P)` are contracting in the sense below. Both remain separate obligations;
see "Relation to the source" below.

## Data and conventions

`D : StablePairingData G` supplies subgroups `N`, `Nbar`, `M` of a topological
group `G`, with `M` normalizing `N` and `Nbar`. It also supplies an element `g`
commuting with `M` and a predicate `Good` on open subgroups. Good subgroups are
compact, form a neighbourhood basis of `1`, are stable under conjugation by `M`,
factor as `K = (K ∩ Nbar)(K ∩ M)(K ∩ N)`, and satisfy
`g⁻¹ (K ∩ Nbar) g ⊆ K` and `gʳ (K ∩ N) g⁻ʳ ⊆ K` for all `r`. They are also deep:
for good `K₀, K₁` some power `gʳ` conjugates `K₀ ∩ N` into `K₁`.

The representation `ρ` of `G` on a complex vector space `V` is smooth (`hρ`), and
`hA : D.Admits ρ hρ` is the Library's stable-duality and canonical-lift
hypothesis. The Library's `admits_of_iwahoriContractions` derives it from
admissibility of `ρ` and Iwahori contractions (`IsIwahoriContraction`) of every good
subgroup in both orientations, by `g` and by `g⁻¹`.

The pairing is a bilinear form
`b : Coinvariants (smoothContragredient ρ) N →ₗ Coinvariants ρ Nbar →ₗ ℂ`.
`[ℓ]` denotes `Jacquet.mk (smoothContragredient ρ) N ℓ` and `[v]` denotes
`Jacquet.mk ρ Nbar v`. `D.IsStablePairing ρ hρ b` (Library) means
`b [ℓ] [t] = ℓ(t)` for every good `K`, every `K`-fixed smooth functional `ℓ` and
every `t` in the stable image of compression by `g⁻¹` on `K`-fixed vectors.
`exists_isStablePairing` constructs such a `b`.

Comparison with the source: Waldspurger's `V_P` (coinvariants of `V` for the
unipotent radical `U` of `P`) is `Coinvariants ρ Nbar`, so `Nbar` plays the role
of `U`. Waldspurger's `V̌_P̄` (coinvariants of the smooth dual for the opposite
radical `Ū`) is `Coinvariants (smoothContragredient ρ) N`, so `N` plays the role of
`Ū`. The arguments of the pairing are in the opposite order:
`b(ǰ_P̄(v̌), j_P(v))` corresponds to `⟨j_P(v), ǰ_P̄(v̌)⟩_P`. An element `a ∈ A_M`
with `|α(a)|_F < 1` for `α ∈ Δ(P)` contracts `U` under conjugation and its inverse
contracts `Ū`. That is the shape of `IsContractingElement` below.

## Contracting elements

`D.IsContractingElement a` (definition) is the conjunction of four clauses:

- `a` commutes with every element of `M`;
- `a` commutes with `g`;
- for every good `K`, `a l a⁻¹ ∈ K` for all `l ∈ K ∩ Nbar`;
- for every good `K`, `a⁻¹ u a ∈ K` for all `u ∈ K ∩ N`.

`isContractingElement_inv` shows that `g⁻¹` is contracting.

## Helpers

- `exists_finset_averageMap_apply_eq_zero` (in `Langlands.Jacquet`): `ρ` is smooth,
  `N` is any subgroup, and `K` is a compact open subgroup. For `w` in the span
  `relations ρ N` of the vectors `ρ(n)u - u`, there is a finite set `F ⊆ N` such that
  the `K`-average of `ρ(a) w` is zero for every `a` with `a n a⁻¹ ∈ K` for all
  `n ∈ F`. The proof is by induction over the span. For a generator, `ρ(a)ρ(n)u`
  equals `ρ(a n a⁻¹)ρ(a)u`, and the average absorbs `ρ(a n a⁻¹)`. Sums take the union
  of the finite sets.
- `factor_swap`: a good `K` also factors as `(K ∩ N)(K ∩ M)(K ∩ Nbar)`, by applying
  the factorization to `k⁻¹`.
- `compressedAction_commute`: let `K` be good and let `a` commute with `M` and with
  `g`. Assume `a (K ∩ Nbar) a⁻¹ ⊆ K` and `a⁻¹ (K ∩ N) a ⊆ K`. Then compression by `a`
  on `K`-fixed vectors commutes with compression by `g⁻¹`. Both products equal
  compression by `a g⁻¹ = g⁻¹ a`, by the Library's
  `compressedAction_mul_of_factor` applied to the swapped factorization, with the
  roles of `N` and `Nbar` exchanged.
- `compressedAction_mem_stableImage_inv`: under the same hypotheses, compression by
  `a` maps the stable image of compression by `g⁻¹` into itself.
- `mk_averageMap_apply`: let `K` be good and `v` be `K`-fixed. Let `a` commute with
  `M`, and assume `a⁻¹ (K ∩ N) a ⊆ K`. Then the `K`-average of `ρ(a) v` has the same
  class in `Coinvariants ρ Nbar` as `ρ(a) v`. The vector `ρ(a) v` is fixed by
  `K ∩ N` and by `K ∩ M`, so each `K`-translate of it is an `Nbar`-translate.

## Main results

`b` is a stable pairing (`hb : D.IsStablePairing ρ hρ b`) and `hA : D.Admits ρ hρ`
is assumed throughout this section.

- `IsStablePairing.exists_finset_asymptotics`. Let `K` be good, `v` a `K`-fixed
  vector and `ℓ` a `K`-fixed smooth functional. There is a finite set `F ⊆ Nbar`
  with the following property. Let `a` commute with `M` and with `g`, and assume
  `a (K ∩ Nbar) a⁻¹ ⊆ K`, `a⁻¹ (K ∩ N) a ⊆ K` and `a n a⁻¹ ∈ K` for all `n ∈ F`.
  Then `ℓ(ρ(a) v) = b [ℓ] [ρ(a) v]`.

  Proof. The Library's `exists_stable_mk_eq` gives a stable `t` (for `g⁻¹` and `K`)
  with `[t] = [v]`. Then `v - t` lies in `relations ρ Nbar`, and the first helper
  gives `F`. For such an `a`, the `K`-average of `ρ(a) v` equals compression by `a`
  of `t`, which is stable by `compressedAction_mem_stableImage_inv`. Since `ℓ` is
  `K`-fixed, `ℓ(ρ(a) v)` equals `ℓ` of this average (`smoothDualPairing_averageMap`).
  The stable-pairing property turns this value into `b [ℓ] [average]`, and
  `mk_averageMap_apply` identifies the class of the average with `[ρ(a) v]`.
- `IsStablePairing.exists_pow_asymptotics`: for every `v ∈ V` and every smooth
  functional `ℓ`, there is `r₀` with `ℓ(ρ(g⁻¹ ^ r) v) = b [ℓ] [ρ(g⁻¹ ^ r) v]` for all
  `r ≥ r₀`. This version needs no condition on finite subsets of `Nbar`.

  Proof. Choose a good `K` fixing `v` and `ℓ` and a stable `t` with `[t] = [v]`.
  The `lower_kernel` field of `Admits` puts `v - t` in the supremum of the kernels of
  the powers of compression by `g⁻¹`. These kernels increase, so some power `r₀` kills
  `v - t`. Hence every power `r ≥ r₀` sends `v` and `t` to the same stable vector.
  The Library's `compressedAction_inv_pow_apply` identifies this vector with the
  `K`-average of `ρ(g⁻¹ ^ r) v`. Then argue as above, with `a = g⁻¹ ^ r` in
  `mk_averageMap_apply`.
- `HasAsymptotics D ρ b` (definition) is the asymptotic property of an arbitrary
  bilinear form `b`. For every good `K`, every `K`-fixed `v` and every `K`-fixed
  smooth functional `ℓ`, there is a finite set `F ⊆ Nbar` such that
  `ℓ(ρ(a) v) = b [ℓ] [ρ(a) v]` for every `a` with `D.IsContractingElement a` and
  `a n a⁻¹ ∈ K` for all `n ∈ F`.
- `IsStablePairing.hasAsymptotics`: under `hA` and `hb`, `D.HasAsymptotics ρ b`.
- `HasAsymptotics.exists`: if `ρ` is smooth and `D.HasAsymptotics ρ b`, then for every
  `v` and every smooth functional `ℓ` there are a good `K` and a finite set `F ⊆ Nbar`
  such that the formula holds for every contracting `a` with `a n a⁻¹ ∈ K` for all
  `n ∈ F`. A common good subgroup fixes `v` and `ℓ` because good subgroups form a
  neighbourhood basis.
- `HasAsymptotics.normalized`: assume `D.HasAsymptotics ρ b`, and let
  `δ : M →* ℝ≥0ˣ` be a character. Let `K` be good, `v` a `K`-fixed vector and `ℓ` a
  `K`-fixed smooth functional. Then there is a finite set `F ⊆ Nbar` such that, for
  every `a ∈ M` with `D.IsContractingElement a` and `a n a⁻¹ ∈ K` for all `n ∈ F`,
  `ℓ(ρ(a) v) = δ(a)^{1/2} · b [ℓ] (J_δ(a) [v])`. Here `J_δ` is the Library's
  `normalizedActionOfModulus ρ Nbar M _ δ`, with
  `J_δ(m) [v] = δ(m)^{-1/2} [ρ(m) v]`. With `δ = δ_P`, `J_δ` is Waldspurger's
  `π_P`, and the identity is the source formula
  `⟨π_P(a) j_P(v), ǰ_P̄(v̌)⟩_P = δ_P(a)^{-1/2} ⟨π(a)v, v̌⟩`.
- `exists_nondegenerate_invariant_hasAsymptotics`: under `hA` alone, there is a
  bilinear form `b` with all four of the following properties:
  - `b` is injective (nondegenerate on the side of the smooth dual);
  - `b.flip` is injective (nondegenerate on the side of `V`);
  - `b (m · x) (m · y) = b x y` for every `m ∈ M`, for the unnormalized descended
    actions `action` on the two quotients;
  - `D.HasAsymptotics ρ b`.

  The form is the stable pairing of `exists_isStablePairing`. The first three
  properties are the Library's `IsStablePairing.injective`,
  `IsStablePairing.flip_injective` and `IsStablePairing.map_action`; the last is
  `IsStablePairing.hasAsymptotics`. This is the abstract form of Théorème I.4.1.
  Invariance is stated for the unnormalized descended actions only.

## Relation to the source

The formula is proved for the abstract class of contracting elements, controlled by
a finite subset `F` of `Nbar` and the good subgroup `K`. Waldspurger's cone is
`{a ∈ A_M : |α(a)|_F < ε for all α ∈ Δ(P)}`. To specialize, one has to construct
`StablePairingData` for `P = MU` on actual rational points, with `Nbar = U`,
`N = Ū`, `M` the Levi subgroup and a strictly contracting `g ∈ A_M`, and to prove
`Admits`. One also has to show two facts about the cone: elements of `A_M` with
`|α(a)|_F ≤ 1` for all `α ∈ Δ(P)` are contracting for the chosen good subgroups;
and for a finite `F ⊆ U` and a compact open `K`, `a F a⁻¹ ⊆ K` once every
`|α(a)|_F` is small enough. None of this is done here. For the block parabolic
subgroups of `GL_n` the Library already constructs the pairing data
(`standardPairingData_admits`, `refinedPairingData_admits`). The uniform
block-chamber asymptotics for `GL_n` are the separate Library statement
`Langlands.Parabolic.CanonicalPairingClause`, which this module does not prove.

Waldspurger also does not assert uniqueness of the pairing, and the module proves
none.
