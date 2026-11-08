# The restricted building of a Tits system is polysimplicial

This module proves, for a supplied abstract Tits system
`h : IsTitsSystem B N π S` with `S` finite, the polysimplicial part of KP
Proposition 1.5.18(3). The admissible parabolic subgroups, ordered by reverse
inclusion, are order isomorphic to the facets of an explicit polysimplicial
complex whose factors are indexed by the irreducible components of `S`. The
group `G` and the Weyl group `W` have independent universes. The proof follows
KP Lemma 1.4.9, Proposition 1.4.10 and the proof of Proposition 1.5.18
(book pp. 49–50 and 61–62), but it constructs the component buildings
directly instead of first forming the Tits systems `(G, G_{Sᵢᶜ}, N, Sᵢ)` of KP
Lemma 1.4.8. It is an internal deduction from the existing Tits-system API and
the frozen `TitsSystemExchange` parabolic lattice.

## Components

`SameComponent S` is the existing reflexive–transitive closure of
noncommutation in `S`. `sameComponent_symm` proves it symmetric, so
`componentSetoid S` is an equivalence relation on the subtype `S`.
`Component S` is its quotient, `componentOf` the class map and
`componentSet c ⊆ S` the elements of `S` in the class `c`. These are the
`Sᵢ` of KP §1.4 (the parts of the smallest decomposition of `S` into mutually
commuting subsets). The quotient is finite when `S` is finite.

The basic lemmas say that each `componentSet c` is nonempty, that an element of
`S` lies in exactly one component, and that elements of different components
commute (`commute_of_not_mem_componentSet`). `isAdmissibleType_iff` restates
the existing `IsAdmissibleType S X` as: `X ⊆ S` and every component contains
an element outside `X`. This is KP Definition 1.5.17(1).

## Product decompositions

`commute_of_mem_closure` shows that commuting generating sets generate
commuting subgroups, using Mathlib centralizers. Let `T ⊆ S` be such that its
elements commute with those of `S \ T`. `exists_mul_eq_of_commute` proves by
closure induction that every `w ∈ W` is `u v` with `u ∈ W_{S \ T}` and
`v ∈ W_T`. `exists_mul_eq_standardParabolic` lifts this through the Bruhat
cell of `g` to `g = y z` with `y ∈ G_{S \ T}` and `z ∈ G_T`.

`exists_forall_inv_mul_mem` is the surjectivity step in the proof of KP
Proposition 1.4.10, extended to finitely many components: for any family
`g_c` indexed by the components there is `x` with
`g_c⁻¹ x ∈ G_{S \ S_c}` for every `c`. The proof is induction over a finite set
`J` of components. Given `x` for `J` and a new component `m`, let `T` be the
union of the components in `J`. The decomposition gives
`x⁻¹ g_m = y z` with `y ∈ G_{S \ T}` and `z ∈ G_T`. Then `x y` works: for
`c ∈ J` it multiplies on the right by `y ∈ G_{S \ T} ≤ G_{S \ S_c}`, and
`g_m⁻¹ x y = z⁻¹ ∈ G_T ≤ G_{S \ S_m}`.

## Component buildings

Several general lemmas on the Library's `conjugateSubgroup` are proved:
membership, cancellation of inverse conjugation, monotonicity and the
order-reflection law.

`maximalParabolic g s` is `g G_{S \ {s}} g⁻¹`. A vertex of the component
`c` (`IsComponentVertex`, type `ComponentVertex c`) is such a subgroup with
`s ∈ componentSet c`. Its type is `S \ {s} = Sᵢᶜ ∪ (Sᵢ \ {s})`, a maximal
proper type of the Tits system `(G, G_{Sᵢᶜ}, N, Sᵢ)` of KP Lemma 1.4.8. These
are the vertices of the component building `Bᵢ`. `componentFace c P` is the
set of vertices of `c` containing `P`.

`conjugate_le_iff_of_isComponentVertex` is the key computation. For
`X ⊆ S`, a vertex `Q` of `c` contains `g G_X g⁻¹` if and only if
`Q = g G_{S \ {s}} g⁻¹` for some `s ∈ componentSet c` with `s ∉ X`. In the
forward direction, write `Q = k G_{S \ {t}} k⁻¹`. Conjugating by `g⁻¹` puts
`G_X ⊇ B` inside `(g⁻¹k) G_{S \ {t}} (g⁻¹k)⁻¹`. The existing rigidity lemma
`mem_of_eq_conjugate` puts `g⁻¹k` in that overgroup of `B`, so it equals
`G_{S \ {t}}`. Hence `Q = g G_{S \ {t}} g⁻¹`, and the lattice criterion
`standardParabolicSubgroup_le_iff` gives `t ∉ X`. `maximalParabolic_eq_iff`
shows that distinct elements of `S` give distinct vertices.
`maximalParabolic_mul_of_mem` shows that right multiplication of `g` by an
element of `G_{S \ {s}}` does not change the vertex.
`exists_eq_conjugate_of_isAdmissibleParabolic` writes every admissible
parabolic subgroup as `g G_X g⁻¹` with `X` admissible.

`componentComplex c` is the simplicial complex on `ComponentVertex c` whose
faces are the sets `componentFace c P` for admissible parabolic subgroups
`P`. With `P = g G_X g⁻¹`, this face consists of the distinct vertices
`g G_{S \ {s}} g⁻¹` for `s ∈ S_c \ X`. It is finite because `S` is finite,
and nonempty because `X` is admissible. A vertex `k G_{S \ {s}} k⁻¹` is the
face of `k G_{S_c \ {s}} k⁻¹`; this type is admissible because it misses `s`
in `c` and every element of every other component. A nonempty subset `τ` of
the face of `g G_X g⁻¹` is the face of `g G_{X'} g⁻¹`, where
`X' = (X \ S_c) ∪ (S_c \ T)` and `T` is the set of `s ∈ S_c` whose vertex
lies in `τ`. `X'` is admissible because it agrees with `X` outside `S_c` and
misses the nonempty set `T` in `S_c`. These faces are the simplices of the
Tits building of `(G, G_{Sᵢᶜ}, N, Sᵢ)` in the description of KP
Proposition 1.5.6 and Remark 1.5.7: the maximal proper parabolic subgroups
containing a given proper parabolic subgroup.

## The polysimplicial complex

`restrictedComplex` is the polysimplicial complex with factors
`componentComplex c` (KP Definition 1.5.1(2)). `restrictedBox P` is the
product over components of `componentFace c P`. It is a facet for every
admissible `P`.

`le_of_componentFace_subset`: if every component face of an admissible
`P = g G_X g⁻¹` is contained in the corresponding face of `P'`, then
`P' ≤ P`. Take `x ∈ P'`, a Bruhat cell `C(w)` of `g⁻¹ x g`, and an `S`-reduced
word for `w`. If a letter `y` were outside `X`, the vertex
`g G_{S \ {y}} g⁻¹` would contain `P`, hence `P'` and `x`. Then `w` would lie
in `W_{S \ {y}}`, and the letter property of `TitsSystemExchange` would put
`y` in `S \ {y}`. So all letters lie in `X`, `w ∈ W_X` and `x ∈ P`. With the
existing inclusion criterion for products of simplices, `restrictedBox_subset_iff`
proves `restrictedBox P ⊆ restrictedBox P' ↔ P' ≤ P` for admissible `P`.

`exists_restrictedBox_eq` proves that every facet of `restrictedComplex` is
`restrictedBox P` for an admissible `P` (KP Proposition 1.4.10,
surjectivity). Choose admissible `P_c = g_c G_{X_c} g_c⁻¹` realizing the
factor of each component. Let `x` be a common point given by
`exists_forall_inv_mul_mem`, and let `Y` be the union of the sets
`S_c ∩ X_c`. Then `Y` is admissible, and on `S_c` it agrees with `X_c`. Since
`g_c⁻¹ x ∈ G_{S \ S_c} ≤ G_{S \ {s}}` for `s ∈ S_c`, the vertices
`x G_{S \ {s}} x⁻¹` and `g_c G_{S \ {s}} g_c⁻¹` coincide. Thus
`x G_Y x⁻¹` has the prescribed face in every component.

`restrictedFacetOrderIso` is the resulting order isomorphism from the
admissible parabolic subgroups with the opposite inclusion order (the facets of
the restricted building in the parabolic description of KP Remark 1.5.7) to the
facets of `restrictedComplex` ordered by inclusion. The map is
`P ↦ restrictedBox P`. Its inverse chooses a parabolic produced by
`exists_restrictedBox_eq`. The two directions of `restrictedBox_subset_iff`
make this choice inverse and give the order condition.

## Scope

The results concern an arbitrary supplied Tits system with finite `S`. They do
not treat the apartments of the restricted building, the action of
automorphisms of `G`, or KP Proposition 1.5.18(1), (2) and (4). They construct
no realization of a valuation quotient. They also prove no witness of
`RootValuationBuildingConstructionStatement`.
