# Partners in the simple-root fiber of a multipliable relative root

Module `Langlands.GroupScheme.Rational.SimpleRootFiberPartners`, namespace
`Langlands.GroupScheme.SimpleRootFiber`.

Worker 163, for Task 6836 (8c04a3ed-3fa6-4680-a59f-856738cb578b), SU3 half.

## Purpose

The SU3 clause of `AlgebraicRankOneCoordinatesExistenceStatement` concerns a simple relative
root `a` such that `2 • a` is also a relative root. This module sets up the combinatorics of
the fiber of `a` for the pinning `fiberPinning` of `SimpleRootFiberPinning`. The fiber
`O = fiberSet a` consists of the simple roots of `fiberPinning` that restrict to `a`. The
fiber field is `L = fiberField`, the field of the base root `β₀`. The embeddings are
`τ_t = fiberEmbedding t : L →ₐ[k] K`.

The module proves these facts:

- every member `t` of `O` has exactly one partner `π t`: the only member of `O` other than
  `t` that is not orthogonal to `t`;
- `t` and `π t` pair to `-1` in both directions, so they span a root system of type `A₂`;
- every other member of `O` is orthogonal to `t`;
- every absolute root over `2 • a` has the form `β_t + β_{π t}` with `t ∈ O`;
- the field `E` of the root `β₀ + β₀'` is a subfield of `L`, and `L/E` is a separable
  quadratic extension;
- `τ_{π t}` is `τ_t` composed with the conjugation of `L/E`.

These are the root-theoretic inputs for building `SU₃(L/E) → G(k)`. In the literature this is
the classification of rank-one relative root systems of type `BC₁`. Each Galois orbit of the
simple roots over `a` is a union of `A₂` pairs swapped by Galois, with the other pairs
orthogonal. See Borel–Tits, *Groupes réductifs* §4, and Kaletha–Prasad, *Bruhat–Tits
theory*, Prop. 7.1.1 and its proof. The Lean development is internal. It uses the Library
results cited below and no source text.

## Standing assumptions

The variables are those of `SimpleRootFiberPinning` and `SimpleRootFiberCoroot`:

- `K/k` is a finite Galois extension;
- `f ≫ j : S ⟶ G` is a maximal split torus (`hf`) whose centralizer is represented by the
  torus `j : T ⟶ G` (`hcent`), and `j` is closed (`hjc`);
- `P` is a reduced root datum of `(G_K, T_K)` (`hP`); `T_K` is split (`hT`), `G_K` is
  connected reductive (`hGK`) and `j_K` is a maximal torus (`hi`);
- `ν` is a generic cocharacter and `a ∈ simpleRelativeRoots (f ≫ j) ν` (`ha`).

`Dₚ = fiberPinning …` is the Galois-compatible pinning with action
`Dₚ.action σ` on the simple roots. Notation in the source: `Oₐ` is the fiber, `π` the partner
map, `p₀` the base point (`basePoint`), `β₀`/`β₀'` the base root and its partner's root,
`L₀ = fiberField` and `E₀ = pairField`.

## The action (section `Action`)

- `fiberPinning_isPairingCompatible`: `Dₚ.action` preserves pairings in the sense of
  `RootDatumOrbitPairs.IsPairingCompatible`, from
  `GaloisCompatiblePinningData.ofRegularCocharacter_isPairingCompatible`.
- `fiberPinning_action_root`: the root of `Dₚ.action σ t` is the Galois transport of the
  root of `t` (`IsRootDatumOf.descendedRegularCocharacterSimpleAction_root`).
- `fiberPinning_pairing_action`: `⟨σ t, σ t'⟩ = ⟨t, t'⟩`.

## The partner map (section `Partner`)

- `partner t` (definition, classical): if some `Dₚ.action σ t` differs from `t` and is not
  orthogonal to `t`, then `partner t` is one such element. Otherwise `partner t = t`.
- `partner_spec`: if such a companion exists, `partner t` is one, and it is reached from `t`
  by the action.

## The fiber of a multipliable root (section `Field`)

Assume in addition `[IsGalois k K]`, `hjc` and `ha`.

- `exists_action_eq`: any two members of `O` are related by the action. This uses
  `baseRoot_orbit`: the fiber is one Galois orbit.

Assume further `h2a : 2 • a ∈ relativeRoots (f ≫ j)`.

- `root_add_root_notMem`: `2 β` is never a root
  (`RootPairNoncommutation.hasNoHigherRoots`).
- `exists_companion`: every `t ∈ O` has a non-orthogonal companion `Dₚ.action σ t ≠ t`. By
  `MultipliableRootNoncommutation.exists_partner` there are roots `r ≠ r'` over `a` with
  `r' = σ r` and `⟨r, r'⟩ = -1`. Their members `s, s'` of `O` satisfy `s' = σ s`. Conjugating
  by an element `γ` with `γ s = t` gives the companion `γσγ⁻¹ t` of `t`.
- `partner_spec_of_mem`, `partner_ne`, `not_isOrthogonal_partner`, `partner_mem`: for
  `t ∈ O`, the partner is a non-orthogonal companion different from `t`, and it lies in `O`.
- `pairing_partner`: `⟨t, π t⟩ = ⟨π t, t⟩ = -1`, by
  `RootDatumOrbitPairs.pairing_eq_neg_one_of_not_isOrthogonal`.
- `eq_partner_of_not_isOrthogonal`: a member `t' ≠ t` of `O` that is not orthogonal to `t` is
  `π t`. This is the uniqueness `RootDatumOrbitPairs.eq_of_not_isOrthogonal`.
- `isOrthogonal_of_ne_partner`: members of `O` other than `t` and `π t` are orthogonal to
  `t`.
- `partner_partner`: `π (π t) = t`.
- `partner_action`: `π (σ t) = σ (π t)`.
- `exists_root_eq_add_partner`: `β_t + β_{π t}` is a root
  (`RootDatumOrbitPairs.exists_root_eq_add_of_not_isOrthogonal`).
- `exists_mem_root_eq_add_partner` (**roots over `2 • a`**): if the root `β_m` restricts to
  `2 • a`, then `β_m = β_t + β_{π t}` for some `t ∈ O`. The proof uses Galois orbit sums.
  Since `β_m` and `2 β_{p₀}` have the same restriction, their orbit sums agree
  (`IsLargestSplitSubtorus.galoisOrbitSum_eq_of_restrict_eq`). Orbit sums of roots are
  nonzero (`RootPartnerFields.orbitSum_ne_zero`). Then
  `RootPairing.OrbitPartner.exists_root_eq_add_of_orbitSum_eq_two_nsmul` writes `β_m` as a
  sum of two roots in one orbit, and `isOrbitPartner_of_root_eq_add` makes them distinct and
  non-orthogonal. Both summands restrict to `a`. Their members `s, s'` of `O` satisfy
  `s' = π s` by `eq_partner_of_not_isOrthogonal`.
- `baseRoot_add_partner_mem`, `pairRoot` (definition): `β₀ + β₀'`, the sum of the roots of
  the base point and its partner, as an element of `roots j_K`. Its restriction is `2 • a`.
- `pairField` (abbreviation): `E = rootOrbitField pairRoot`, the fixed field of the
  stabilizer of `β₀ + β₀'`.
- `baseRoot_isRootPartner`: `β₀` and `β₀'` are root partners in the sense of
  `RootPartnerFields.IsRootPartner` (same orbit, distinct, sum a root).
- `galoisOrbitSum_ne_zero`: no root of `T_K` in `G_K` has zero Galois orbit sum (from
  `root_restrict_ne_zero_of_torusCentralizer`). It needs neither `IsGalois` nor
  `FiniteDimensional`.
- `pairField_le`: `E ≤ L` (`RootPartnerFields.rootOrbitField_le`).
- Instances `pairAlgebra : Algebra E L` (the inclusion, via
  `QuadraticFixedFields.nestedAlgebra`), `pairField_isScalarTower : IsScalarTower E L K`,
  `pairField_isScalarTower_base : IsScalarTower k E L`,
  `pairField_isQuadraticExtension : Algebra.IsQuadraticExtension E L`
  (`RootPartnerFields.isQuadraticExtension`) and
  `pairField_isSeparable : Algebra.IsSeparable E L` (`RootPartnerFields.isSeparable`).
- `fiberEmbedding_partner`: `τ_{π t} x = τ_t (SU3Root.conjugation E L x)` for `t ∈ O` and
  `x ∈ L`. Write `t = γ p₀` and `π p₀ = σ p₀`. Then `π t = γ σ p₀` (`partner_action`), and
  `fiberEmbedding_galois` reduces the claim to `σ x = conj x` on `L`. That is
  `RootPartnerFields.conjugation_apply` for the root partners `β₀`, `σ β₀ = β₀'`.
- `fiberEmbedding_partner_algebraMap`: `τ_t` and `τ_{π t}` agree on `E`.

## Provenance

Internal glue for Task 6836. The mathematical statements are standard facts about
quasi-split groups with a non-reduced relative root system (Borel–Tits §4; Kaletha–Prasad
Prop. 7.1.1). The Lean proofs combine the Library modules `RootDatumOrbitPairs` (unique
non-orthogonal companion in a pairing-compatible orbit), `QuasiSplitPinningOrbitPairs`,
`MultipliableRootNoncommutation.exists_partner`, the orbit-partner lemmas of
`Reductive/RootDatumOrbitPartners` and `Reductive/RootDatumOrbitSums`, and
`RootPartnerFields` (quadratic pair field and its conjugation). Every step is proved in
Lean, with no new axioms.
