# Evaluating a stable-lift pairing at translates

`Langlands/Representation/Aubert/General/StableLiftAsymptotics.lean` proves the abstract
core of the asymptotic formulas (VI.9.6.4) and (VI.9.6.5) in Renard 2026, VI.9.6
(Proposition, printed p.202 / PDF p.208; its proof of the two formulas is on printed
p.205 / PDF p.211). It defines the predicate `HasStableLifts` and works with an abstract
pairing for which a vector has stable lifts, the property recorded by
`IsStableLiftDuality` in
`Langlands/Representation/Aubert/General/IwahoriJacquetStableLift.lean`. It proves no
statement about parabolic subgroups, split components or `C_A^{++}`, and it does not prove
`LeviJacquetOppositePairingStatement`. Those steps remain separate obligations; they are
listed at the end.

## Setting

`G` is a topological group (no local compactness or nonarchimedean hypothesis is used),
`ρ : Representation ℂ G V` is an arbitrary complex representation (smoothness of `ρ` is
not needed), `SmoothDual ρ` is its space of smooth functionals, `smoothContragredient ρ`
its smooth contragredient action `ρ̃` and `smoothDualPairing ρ ℓ w = ℓ(w)` the evaluation.
`Jacquet.Localization.mk ρ O 1` is the quotient map onto the untwisted `O`-coinvariants.

## Definition

`HasStableLifts ρ U M O g P x`, for subgroups `U, M, O` of `G`, an element `g`, a
function `P : SmoothDual ρ → V → ℂ` and a vector `x`, is the proposition: there is an open
subgroup `W` of `G` such that every compact open subgroup `K ≤ W` with
`IsIwahoriContraction K U M O g` and `IsIwahoriContraction K O M U g⁻¹` contains a
`K`-fixed vector `v` (that is, `v ∈ fixedVectors ρ K`) with

* the same `O`-class as `x`: `Jacquet.Localization.mk ρ O 1 v = Jacquet.Localization.mk ρ O 1 x`;
* `P Λ v = Λ(v)` for every `K`-fixed smooth functional `Λ`.

When `P ℓ w` is the pairing of `Ψ(j_U ℓ)` with `j_O w`, this is what
`IsStableLiftDuality` states for the class `j_O x` (with `A` the given representation).
This file does not prove that implication; it only uses `HasStableLifts` as a hypothesis.
The definition is internal to this development; Renard has no named counterpart.

## Two elementary lemmas

* `smoothContragredient_conj_fixed`: if `ρ̃(t c t⁻¹) ℓ = ℓ`, then `c` fixes `ρ̃(t⁻¹) ℓ`.
  This follows from `c t⁻¹ = t⁻¹ (t c t⁻¹)`.
* `smoothDualPairing_sub_eq_zero_of_fixed`: if `ρ̃(o) ℓ = ℓ`, then
  `ℓ(ρ(o) w - w) = 0` for every `w`. This is the invariance
  `smoothDualPairing_invariant` of the evaluation pairing.

## Main theorem

`exists_compact_forall_stableLiftPairing_translate_eq` takes:

* subgroups `U, M, O` of `G`, with `O` closed, and an element `g` such that
  `HasOppositeIwahoriContractionBasis U M O g` holds: every identity neighborhood
  contains a compact open subgroup `K` with Iwahori contractions for `g` in the order
  `(U, M, O)` and for `g⁻¹` in the order `(O, M, U)`;
* a function `P : SmoothDual ρ → V → ℂ` such that `P ℓ w` depends only on the `O`-class
  of `w` (`hPO`) and only on the `U`-class of `ℓ` in the coinvariants of the
  contragredient (`hPU`);
* a vector `x` with `HasStableLifts ρ U M O g P x` (`hx`);
* a smooth functional `ℓ`.

It concludes that there is a compact set `C ⊆ O` with the following property. Let `t` be
any element that normalizes `O`, commutes with every element of `M`, satisfies
`ρ̃(t c t⁻¹) ℓ = ℓ` for every `c ∈ C`, and satisfies the translation law
`P (ρ̃(t⁻¹) ℓ') w = P ℓ' (ρ(t) w)` for all `ℓ'` and `w`. Then

`P ℓ (ρ(t) x) = ℓ(ρ(t) x)`.

The set `C` depends on `x` and `ℓ` but not on `t`; this is what lets a uniform contraction
estimate for `t` give the formula for all `t` at once.

## Proof

1. `ℓ` is fixed by an open subgroup `L`. Let `W` be the open subgroup given by
   `HasStableLifts`. Choose, by the basis hypothesis, a compact open `K ⊆ W ∩ L` with
   both contractions, and a stable lift `v` of `x` for this `K`.
2. `x - v` lies in the relation span of the `O`-coinvariants. Write it as a finite
   combination `Σ f_i (ρ(o_i) w_i - w_i)` with `o_i ∈ O`. Put
   `C = (K ∩ O) ∪ {o_i}`. This set is compact because `K` is compact and `O` is closed,
   and it lies in `O`.
3. Fix `t` as in the conclusion and put `ℓ_t = ρ̃(t⁻¹) ℓ`. By the first lemma `ℓ_t` is
   fixed by every element of `C`. It is also fixed by `K ∩ M`: such an `m` commutes with
   `t`, and `m ∈ K ⊆ L` fixes `ℓ`.
4. `ℓ(ρ(t) x) = ℓ_t(x)` by the definition of `ρ̃`, and `ℓ_t(x) = ℓ_t(v)` by the second
   lemma applied to the generators `ρ(o_i) w_i - w_i`.
5. Since `t` normalizes `O`, translation by `t` preserves the relation span
   (`Jacquet.Localization.relations_stable`). So `ρ(t) x` and `ρ(t) v` have the same
   `O`-class, and `P ℓ (ρ(t) x) = P ℓ (ρ(t) v) = P ℓ_t v` by `hPO` and the translation
   law.
6. Let `Λ` be the `K`-average of `ℓ_t` (`Compact.averageMap`); it is `K`-fixed. Each
   `k ∈ K` factors as `k = l m o` with `l ∈ K ∩ U`, `m ∈ K ∩ M` and `o ∈ K ∩ O`, by the
   Iwahori factorization of the `g⁻¹` contraction. Then `ρ̃(k) ℓ_t = ρ̃(l) ℓ_t`, which has
   the same `U`-class as `ℓ_t`. Averaging preserves this class
   (`Jacquet.map_averageMap_of_forall_eq`), so `P ℓ_t v = P Λ v` by `hPU`.
7. `P Λ v = Λ(v)` by the stable-lift property, and `Λ(v) = ℓ_t(v)` because `v` is
   `K`-fixed. Combining with step 4 gives the conclusion.

## Relation to the source

Renard proves (VI.9.6.4) by fixing `K` that fixes `v` and `λ` and using the decomposition
`V^K = V^K_0 ⊕ V^K_*` with its orthogonality relations and sections `s^K_P`, `s^K_P̄`. This
file follows a different route. It uses only the stable-lift property of the pairing,
and it replaces the condition "`m` large" by an explicit compact set `C ⊆ O` that `t`
must conjugate into the stabilizer of `ℓ`. The translation law corresponds to the
`M`-equivariance of `⟨·,·⟩_P` (printed pp.204–205 / PDF pp.210–211), once the
normalizing characters `δ_P^{1/2}` and `δ_P̄^{1/2}` cancel (Renard cites Lemma V.5.4).
The centrality of `t` in `M` corresponds to Renard's use of "`t` est central dans `M`".
The result is therefore a derived supporting theorem, not a statement taken from the
source, and `HasStableLifts` is an internal definition naming its hypothesis.

## Remaining obligations for the parent proposition

Applying this theorem to `LeviJacquetOppositePairingStatement` still needs, outside this
file:

* transporting a stable-lift duality from the abstract normalized Jacquet functor to the
  represented `leviJacquetFunctor`, with an explicit isomorphism `E`;
* the translation law for `t` in the split component, from the `M`-equivariance of `E`
  and the reciprocity of the two inverse-half Haar characters;
* the geometric facts that the split component is central in `M(F)` and that
  conjugation by elements of `C_A^+(ε)` (and by large powers of `t ∈ C_A^{++}`) moves a
  given compact subset of `N(F)` into a given open subgroup.
