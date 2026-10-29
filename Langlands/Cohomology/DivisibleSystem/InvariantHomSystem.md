# Hom systems out of invariants of `ℓ`-divisible systems

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.HomSystem` (`homTransition`,
`homTransition_eq_iff`, `projection_comp_homTransition`, `homSystem`,
`homSystemCone`, `homSystemIsLimit`),
`Langlands.Cohomology.DivisibleSystem.Invariants` (the instances making
`Rep.quotientToInvariantsFunctor k S` additive and limit-preserving, needed by
`mapLeftExact`) and `Langlands.Representation.Induction.QuotientAdjunction`
(`homInvariantsRestriction`, `homInvariantsRestriction_comp_left`,
`homInvariantsRestriction_comp_right`, `homInvariantsRestrictionEquiv`,
`homInvariantsRestrictionEquiv_apply`). Through them it uses
`DivisibleSystem`, `DivisibleSystem.map`, `DivisibleSystem.degree`,
`DivisibleSystem.mapLeftExact` (`LeftExact`), `DivisibleSystem.mapComplexes`
(`Sections`) and `invariantsToCoinvariants` (`InvariantRestriction`). From
Mathlib it uses `Rep.quotientToInvariantsFunctor`, `Rep.resFunctor`,
`NatIso.ofComponents`, `LinearEquiv.toModuleIso`, `IsLimit.map`,
`IsLimit.map_π`, `IsLimit.conePointsIsoOfNatIso`,
`IsLimit.conePointsIsoOfNatIso_hom_comp` and `Iso.toLinearEquiv`.

All new names are in the namespace `Langlands.Cohomology.DivisibleSystem`.
`k : Type u` is a commutative ring, `G : Type v` a group and `S` a normal
subgroup of `G`. All representations have carriers in one universe `w`
(`Rep.{w}`).

## Conventions

`T` is an `ℓ`-divisible system in `Rep k G` and `W` an `ℓ`-divisible system
in `Rep k (G ⧸ S)`.

- `Inf W` denotes `W.map (Rep.resFunctor (QuotientGroup.mk' S))`, the
  inflation of `W` to `G`. `map` applies because inflation is additive and
  preserves finite limits and finite colimits.
- `T^S` denotes `T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT`,
  the `ℓ`-divisible system in `Rep k (G ⧸ S)` of `S`-invariants of `T`. Here
  `hT` is the hypothesis that for all `m' ≤ m` the map induced on
  `S`-invariants by the projection `T m ⟶ T m'` is an epimorphism.
- `homSystem k T W` is the inverse system of `k`-modules
  `m ↦ Hom(T m, W m)` of `HomSystem`. Its limit cone `homSystemCone k T W`
  has apex the module of morphisms of inverse systems `T.tower ⟶ W.tower`,
  and `homSystemIsLimit k T W` proves that this cone is a limit.

## Restriction as a morphism of inverse systems

- `homTransition_homInvariantsRestriction hT W h f`: for `m' ≤ m` (`h`) and
  `f : T m ⟶ Inf (W m)`, the transition of the Hom inverse system of `T^S`
  and `W` applied to the restriction of `f` to the `S`-invariants is the
  restriction of the transition of `f` in the Hom inverse system of `T` and
  `Inf W`. By `homTransition_eq_iff` it suffices to check the equality after
  the projection `(T m)^S ⟶ (T m')^S`; this follows from
  `homInvariantsRestriction_comp_left`, `projection_comp_homTransition` and
  `homInvariantsRestriction_comp_right`.
- `invariantsHomSystemHom k S T hT W`: the morphism of inverse systems
  `homSystem k T (Inf W) ⟶ homSystem k T^S W` whose component at `m` is
  `homInvariantsRestriction (T m) (W m)`. Its naturality is the previous
  lemma. `invariantsHomSystemHom_app_apply` states its components on
  elements.
- `invariantsHomSystemIso k S T hT W hbij`: if
  `invariantsToCoinvariants (T m).ρ S` is bijective for every `m` (`hbij`),
  the isomorphism of inverse systems `homSystem k T (Inf W) ≅
  homSystem k T^S W` whose component at `m` is the linear equivalence
  `homInvariantsRestrictionEquiv (T m) (W m) (hbij m)`.
  `invariantsHomSystemIso_hom` states that its forward morphism is
  `invariantsHomSystemHom`.

## Restriction on the limits

- `towerInvariantsRestrictionApp hT W α`: for a morphism of inverse systems
  `α : T.tower ⟶ (Inf W).tower`, the morphism of inverse systems
  `T^S.tower ⟶ W.tower` whose component at `m` is the restriction of
  `α.app m` to the `S`-invariants. Naturality follows from
  `homInvariantsRestriction_comp_left`, the naturality of `α` and
  `homInvariantsRestriction_comp_right`. The generated lemma
  `towerInvariantsRestrictionApp_app` states its components.
- `towerInvariantsRestriction k S T hT W`: the `k`-linear map
  `(T.tower ⟶ (Inf W).tower) →ₗ[k] (T^S.tower ⟶ W.tower)` sending `α` to
  `towerInvariantsRestrictionApp hT W α`. Additivity and compatibility with
  scalars are checked componentwise. The generated lemma
  `towerInvariantsRestriction_apply` states its values.
- `ofHom_towerInvariantsRestriction`: `ModuleCat.ofHom` of
  `towerInvariantsRestriction`, viewed as a map between the apexes of
  `homSystemCone k T (Inf W)` and `homSystemCone k T^S W`, is the map
  `(homSystemIsLimit k T^S W).map (homSystemCone k T (Inf W))
  (invariantsHomSystemHom k S T hT W)` that `invariantsHomSystemHom` induces
  between these limits. Both sides agree after each limit projection, by
  `IsLimit.map_π`.
- `towerInvariantsRestrictionEquiv k S T hT W hbij`: under the bijectivity
  hypothesis `hbij` of `invariantsHomSystemIso`, the `k`-linear equivalence
  `(T.tower ⟶ (Inf W).tower) ≃ₗ[k] (T^S.tower ⟶ W.tower)` obtained from the
  two limit cones and `invariantsHomSystemIso` by
  `IsLimit.conePointsIsoOfNatIso`.
  `towerInvariantsRestrictionEquiv_apply` states that its underlying map is
  `towerInvariantsRestriction`; the proof compares components using
  `IsLimit.conePointsIsoOfNatIso_hom_comp`.

## Systems of complexes

`K` is an `ℓ`-divisible system in `CochainComplex (Rep k G) ℕ`, and `hK` the
hypothesis that for all `m' ≤ m` and every degree `q` the map induced on
`S`-invariants by the degree `q` component of the projection `K m ⟶ K m'` is
an epimorphism. `K.mapComplexes (Rep.quotientToInvariantsFunctor k S) hK` is
then the `ℓ`-divisible system of complexes of degreewise `S`-invariants.

- `degreeInvariantsHomSystemIso k S K hK W j hbij`: for a degree `j`, if
  `invariantsToCoinvariants` is bijective for the degree `j` term of `K m`
  for every `m` (`hbij`), the isomorphism of inverse systems
  `homSystem k (K.degree j) (Inf W) ≅
  homSystem k ((K.mapComplexes (Rep.quotientToInvariantsFunctor k S) hK).degree j) W`.
  It is `invariantsHomSystemIso` for `T = K.degree j`. The degree `j` system
  of the invariants complexes is by definition the system of `S`-invariants
  of `K.degree j`.

For complexes of smooth representations, the published `toRepComplexes`
provides the underlying system of complexes in `Rep`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10, printed p.312
(one-based PDF page 14; Worker 61 read the rendered scanned page): "We may
replace `C^j_m(ẽ)` by `C^j_m(ẽ)^{H_p}` in (4.10.2). Write
`T_m(j, ẽ) = Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ)^{H_p}, Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`.
To check the Mittag-Leffler condition, we first need to study the maps
(4.10.3) `T_{m+1}(j, ẽ) → T_m(j, ẽ)` as `m` varies."

The published `QuotientAdjunction` states the replacement for single
morphisms in `Rep` together with its naturality. In our reading the
replacement must also be compatible with the maps (4.10.3). This module states
that compatibility for the Hom inverse systems of the published `HomSystem`:
`T` plays the role of the system of degree `j` terms, `G` and `S` the roles
of `S(ẽ)` and `H_p ∩ S(ẽ)`, and `W` the role of the coefficients. This
correspondence is ours. Harris takes morphisms over `𝒪/ℓ^m𝒪[S(ẽ)]`, a ring
that varies with `m`; here the ring `k` is fixed (in our reading `k = 𝒪`).
Since `T m` and `W m` are killed by `ℓ ^ m`, their `k`-linear and
`k/ℓ^m k`-linear maps coincide, but this comparison is not formalized. The
module is derived; all definitions and proofs are ours.

## Scope

The module does not construct Harris's modules `C^j_m(ẽ)` or `T_m(j, ẽ)` or
his maps (4.10.3), and does not identify them with the inverse systems used
here. The surjectivity hypotheses `hT`, `hK` and the bijectivity hypotheses
`hbij` are explicit and not derived. At a level `m` where `T m` is
`Rep.of` the compact induction of a trivial representation from an open
subgroup `H ≤ S` of finite index in `S` whose index is a unit of `k`, `hbij`
at `m` is the published `bijective_invariantsToCoinvariants_compactInduced`.
The module works with representations of abstract groups in `Rep`;
smoothness is not considered.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
