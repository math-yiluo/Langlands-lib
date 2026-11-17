# Nonvanishing form of Jacquet's lemma, without admissibility

Author: Worker 733, Task 6639 (`97df9594-40e0-45d8-8f8c-0e7562c6b4de`).

This module proves, without any admissibility or finiteness hypothesis, that
a nonzero vector of the Jacquet module fixed by `K ∩ M` produces a nonzero
`K`-fixed vector of the representation. Here `K` is a compact open subgroup
with an Iwahori decomposition along the parabolic `P = M N`. All results are
unconditional theorems and introduce no new definitions.

## Statements

The first three theorems are abstract. `G` is a topological group, `ρ` is a
smooth complex representation of `G` on `V`, `K` is a compact open subgroup,
and `N`, `M`, `Nbar` are subgroups with `M ≤ normalizer N`. They assume:

- `hfactor`: every `k ∈ K` factors as `k = l * m * u` with `l ∈ K ∩ Nbar`,
  `m ∈ K ∩ M` and `u ∈ K ∩ N` (only existence is used);
- an element `g ∈ M` with `g⁻¹ (K ∩ M) g ⊆ K ∩ M` (`hlevi`);
- `hcontract`: for every open subgroup `L` of `G` there is `s : ℕ` with
  `g^{-s} l g^s ∈ L` for all `l ∈ K ∩ Nbar`.

`Coinvariants ρ N` with the action `action ρ N M hMN` of `M` is the
unnormalized Jacquet module `V_N`. `fixedVectors … (K.toSubgroup.comap M.subtype)`
is its subspace `V_N^{K ∩ M}`.

- `exists_fixedVector_mk_eq_of_contraction`: for every `y ∈ V_N^{K ∩ M}` there
  are `s : ℕ` and `v ∈ V^K` with `mk ρ N v = g^s · y`. This is Renard's
  (VI.9.1.3).
- `nontrivial_fixedVectors_of_contraction`: if `V_N^{K ∩ M}` is nontrivial,
  then `V^K` is nontrivial.
- `contract_of_conjugatePowerNeighborhoodBasis`: the Library predicate
  `BruhatTits.SpecialCompact.ConjugatePowerNeighborhoodBasis K Nbar g⁻¹`
  implies the contraction hypothesis `hcontract` in the form
  `∃ s, ∀ l ∈ K ⊓ Nbar, (g ^ s)⁻¹ * l * g ^ s ∈ L`, for every open subgroup `L`.

The fourth theorem passes from the normalized to the unnormalized Jacquet
module. `G` is locally compact and nonarchimedean, `N` and `M` are closed, and
`K` is compact open.

- `nontrivial_jacquetAction_fixedVectors_of_normalized`: for a smooth
  representation `D` of `G`, if the normalized Jacquet module
  `(Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D` has a nonzero
  `K ∩ M`-fixed vector, then so does the unnormalized module
  `action D.representation N M hMN`.

The last two theorems specialize to the standard parabolics of a connected
reductive group `G` over a nonarchimedean local field `F`. They take a maximal
split torus `i`, a generic cocharacter `ν`, `J ⊆ simpleRelativeRoots i ν`
with a standard cocharacter, and a compact open subgroup `K` of `G(F)`. They
assume `HasIwahoriIntersectionDecomposition K (standardLeviPoints i ν J)
(standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J)`.

- `nontrivial_fixedVectors_of_standardJacquet`: for every smooth
  representation `ρ` of `G(F)`, a nonzero `K ∩ M_J`-fixed vector of the
  unnormalized `N_J`-coinvariants gives a nonzero `K`-fixed vector of `ρ`.
- `nontrivial_fixedVectors_of_standardNormalizedJacquet`: the same for the
  normalized Jacquet module of a smooth representation `D`. The closedness of
  `N_J` and `M_J`, the normalizer inclusion, local compactness and the
  nonarchimedean property of `G(F)` are explicit arguments.

## Proof

`exists_fixedVector_mk_eq_of_contraction`. Lift `y` to `v ∈ V` with
`mk ρ N v = y`. By smoothness, `v` is fixed by some open subgroup `U`. Choose
`s` with `g^{-s}(K ∩ Nbar)g^s ⊆ U`. Then `w = ρ(g^s) v` has three properties:

- `w` is fixed by `K ∩ Nbar`, because `ρ(l) w = ρ(g^s) ρ(g^{-s} l g^s) v`.
- For `m ∈ K ∩ M`, `mk(ρ(m) w) = g^s · y`. Indeed `g^{-s} m g^s ∈ K ∩ M` by
  iterating `hlevi`, so `mk(ρ(m) w) = g^s · (g^{-s} m g^s) · y`, and `y` is
  `K ∩ M`-fixed.
- `mk` is unchanged by elements of `N`.

Writing `k⁻¹ = l m u` by `hfactor`, we get `k = u⁻¹ m⁻¹ l⁻¹`. Hence
`mk(ρ(k) w) = g^s · y` for every `k ∈ K`. The compact average
`Compact.averageMap ρ hρ K hK w` lies in `V^K`. The published
`map_averageMap_of_forall_eq` shows that the linear map `mk ρ N` sends it to
`g^s · y`, since `mk` is constant on the `K`-orbit of `w`.

`nontrivial_fixedVectors_of_contraction` applies this to a nonzero `y`. The
vector `v` is nonzero because `g^s` acts bijectively on `V_N`
(`Representation.apply_bijective`).

`contract_of_conjugatePowerNeighborhoodBasis` uses the neighbourhood-basis
half of the predicate. The second component is a basis of identity
neighbourhoods of `Nbar` formed by the sets `g^{-s}(K ∩ Nbar)g^s`. It is
applied to the open subgroup `L ∩ Nbar` of `Nbar`. The first component puts
the conjugates inside `Nbar`.

`nontrivial_jacquetAction_fixedVectors_of_normalized`. The normalized Jacquet
module is the twist of the localized action by
`HaarModulus.closedInverseHalfCharacter`. That character is trivial on
`K ∩ M` (`NormalizedJacquetBridge.character_trivial`). By
`fixedVectors_twist_eq_of_le_ker`, a twist by a character trivial on `K ∩ M`
has the same `K ∩ M`-fixed vectors. The equivalence
`Jacquet.Localization.trivialEquiv` identifies the localization at `1` with
the coinvariants action, and it is injective.

`nontrivial_fixedVectors_of_standardJacquet`. The factorization hypothesis is
the existence half of the Iwahori decomposition. The element `g` is the
central strict element `centralStrictElement` of a compatible standard split
component from `exists_compatibleStandardSplitComponent`. Since `g` is
central in `M_J`, `hlevi` holds trivially. The contraction follows from the
neighbourhood-basis part of
`IsCompatibleStandardSplitComponent.strictChamber_power_basis_and_exhaustion`
and `contract_of_conjugatePowerNeighborhoodBasis`.
`nontrivial_fixedVectors_of_standardNormalizedJacquet` composes the normalized
and the standard results.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, VI.9.1, formulas (VI.9.1.1)–(VI.9.1.3) (printed
p.196 / PDF p.202). Renard notes that (VI.9.1.3) holds "sans utiliser
l'hypothèse d'admissibilité". The argument refers back to the proof of
Jacquet's lemma in VI.6.1 (printed p.176 / PDF p.182). Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Renard states (VI.9.1.3) for a fixed strictly dominant element `t` and the
projection `j : V → V_N`. Here the strict element is supplied by the
Library's compatible split component. The contraction it needs is the
Library's neighbourhood-basis statement. The nonvanishing corollary and the
transfer from normalized to unnormalized Jacquet modules are immediate
consequences that the source uses implicitly.
