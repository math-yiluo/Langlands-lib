# Actual finite-place parabolic Iwasawa existence: proof

Lean module: `Langlands.Global.FinitePlaceIwasawaProof`.

## Statement

```
theorem Langlands.Global.FinitePlaceGroupPoints.parabolicIwasawaStatement :
    Langlands.Global.FinitePlaceGroupPoints.ParabolicIwasawaStatement.{u}
```

The type is exactly the published proposition of the module
`Langlands.Global.FinitePlaceIwasawaStatement`, at an arbitrary universe `u`,
with no further hypothesis. For every number field `F : Type u`, every actual
group scheme `G` over `Spec F` with `IsConnectedReductive G`, every actual
morphism `p : P ⟶ G` with `IsParabolicSubgroup p` and every finite place `v`,
it gives a subgroup `K` of `FinitePlaceGroupPoints F G v`, the actual points
of `G` in the finite completion `F_v`, such that

1. `K` is compact in the existing topology given by evaluating all global
   regular functions in `F_v`;
2. every compact subgroup of the same group that contains `K` equals `K`;
3. `Set.range (P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v))) *
   (K : Set _) = Set.univ`, the parabolic image being the left factor.

This is the published predicate
`CoordinateCompactPatching.IsLocalIwasawaCompact`. All parabolics are
covered, including the improper one, and no splitness or isotropy is
assumed, so non-split and anisotropic groups are included. The subgroup is
chosen after the parabolic and the place.

## Proof

The proof has three layers.

### The finite-place reduction

`parabolicIwasawaStatement` fixes `F`, `G`, `p` and `v`. It equips
`FiniteCompletion F v` with the valuative relation
`FiniteCompletion.valuativeRel v`. The published
`FiniteCompletion.isNonarchimedeanLocalField v` shows that, with its existing
topology, `F_v` is a nonarchimedean local field. The published
`baseChanged_isConnectedReductive` shows that the actual pullback
`baseChangedGroup F G v` of `G` to `Spec F_v` is connected reductive. The
local existence theorem below, applied to this pullback, gives a subgroup of
its rational points. The published `baseChangeIwasawaCompactOfParabolicProducts`
(module `Langlands.Global.FinitePlaceIwasawaLocalInput`) turns it into the
required subgroup of `FinitePlaceGroupPoints F G v`. That adapter proves
parabolicity of the base change of `p` itself. It uses only the compactness,
compact maximality and product clauses of the local conclusion. It transports
them along the published continuous multiplicative identification of rational
points of the pullback, with the rational-point topology, with
`FinitePlaceGroupPoints F G v`, with the evaluation topology.

### Local existence

`ConstructionReduction.localExistence` states: for every nonarchimedean
local field `F'` and every connected reductive `G'` over `Spec F'`, some
subgroup `K` of `rationalPoints G'` satisfies
`SpecialCompact.IsCompactOpenMaximal F' K` and
`Iwasawa.AlgebraicParabolicProducts K`. The first predicate says that `K` is
compact and open in the rational-point topology and maximal among compact
subgroups. The second says that for every actual parabolic inclusion
`j : P ⟶ G'`, both `P(F') · K` and `K · P(F')` are the whole group.

The proof destructures the published
`Langlands.Geometry.Building.rootValuationBuildingConstruction` at `(F', G')`.
This gives parahoric building data `B`, a polysimplicial realization `R` and an
apartment splitting `T`, together with seven axioms: the building axiom, bounded
open stabilizers, affine apartments, root reflections, the apartment axioms,
compatible apartment facets and the Tits system. The published
`Langlands.Geometry.Building.rootGroupActionAxiom`, applied to `B` and its
apartment axioms, supplies `B.HasZeroFixerGenerators` as its first conjunct.
The other conjunct, `HasRootZeroFixers`, is not used. The witnesses go to
`localExistence_of_witnesses`.

### The special-point stabilizer

`ConstructionReduction.localExistence_of_witnesses` takes these data and the
eight axioms. Its subgroup is `K = B.compactStabilizer (B.apartmentMap x)`, the
stabilizer in the common kernel of the absolute values of the rational
characters of the image `B.apartmentMap x` of a special apartment point `x`.
The special point exists by `exists_isSpecialPoint` for the affine root system
of the apartment. A generic cocharacter `ν` of the maximal split torus comes from
`exists_genericCocharacter`, using smoothness of `G'`. The four internal
arguments are adapted from the private lemmas of
`Langlands.BruhatTits.Iwasawa.AvailableProof`. Here they are restated for bare
witnesses, not for a datum satisfying the group axioms of an available
assignment.

1. *Compact-open maximality* (`compact_open_maximal`). Bounded open
   stabilizers make `K` open and algebraically bounded. Being open, `K` is
   closed, and `IsAlgebraicallyBounded.isCompact_closure` makes it compact.
   The published `metricRealization` turns the seven building witnesses into a
   complete nonpositively curved metric on the reduced building. In that
   metric the group acts by isometries with continuous orbit maps. Let `H ≥ K`
   be a compact subgroup. Its orbit of a point is compact, hence bounded. By
   `completeNPCGeodesic` and `boundedSetStabilizerFixedPoint`, `H` fixes a point
   `z` (`compact_subgroup_fixes`). Since `K` fixes `z`,
   `eq_of_compactStabilizer_fixed_of_special_buildingPoint` gives `z` equal to
   the special point. Its inputs are opposite-factor pairs from
   `rootRankOneFactorization`, injectivity of compatible apartment facets and
   common apartments from the building axiom. Finally
   `compactSubgroup_le_rationalCommonNormKernel` puts `H` in the norm kernel,
   so `H ≤ K`.
2. *Product with the minimal standard parabolic*
   (`minimal_parahoric_products`). Choose a chamber whose closure contains `x`
   (`exists_regularPoint_closure`). The chamber parahoric lies in the parahoric
   `B.parahoricAt x`. The published
   `ParahoricBuildingData.iwasawaDecomposition_of_relativeTitsSystem` writes
   each point as `u n p`, with `u` in the standard unipotent subgroup, `n` in
   the normalizer of the maximal split torus and `p` in the chamber parahoric.
   Its algebraic premises are discharged by `rootRankOneFactorization`,
   `relativeTitsSystem` and `hasSimpleRootParabolicFactorization_of_statements`.
   Specialness of `x` and `HasZeroFixerGenerators` give a representative `m`
   in `B.parahoricAt x` of the relative Weyl class of `n`
   (`SpecialCompact.WeylRepresentatives.special_parahoric_normalizer_surjective`).
   Then `n m⁻¹` centralizes the torus. So `u (n m⁻¹)` lies in the empty-index
   standard parabolic and `m p` lies in `B.parahoricAt x`. The reverse
   product order comes from decomposing inverses.
3. *All actual parabolics* (`algebraic_of_minimal`). The empty-index
   standard parabolic is the dynamic parabolic of the generic cocharacter
   (`standardParabolic_empty_eq_dynamic_of_generic`). It is a minimal parabolic
   (`genericMinimalParabolic`). Every actual parabolic `j` contains a minimal
   parabolic (`parabolicContainsMinimalStatement`). Minimal parabolics are
   rationally conjugate (`minimalParabolicConjugacy`). If `P₀(F') K` and
   `K P₀(F')` are the whole group, the same holds for `g P₀(F') g⁻¹` in place
   of `P₀(F')`. Indeed, write `g = k b` with `k ∈ K` and `b ∈ P₀(F')`; then
   `g P₀(F') g⁻¹ = k P₀(F') k⁻¹`. Enlarging either factor preserves both
   equalities.
4. *Enlarging the parahoric.* The published
   `ParahoricBuildingData.parahoricAt_le_compactStabilizer` puts
   `B.parahoricAt x` inside `K`. It uses the topology compatibility clause of
   the apartment axioms. So the products of step 2 hold with `K` in place of
   the parahoric, before step 3 is applied.

## Route and sources

The proof follows Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Appendix B: Proposition B.4.2 and the first part of
the proof of Theorem B.4.3, printed p.548 (one-based PDF p.553). Theorem B.1.1
and equation (B.1), printed p.541 (PDF p.546), state the Iwasawa
decomposition `G(F) = P(F) K` that clause 3 records. Registered source:
`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`. The
October 2026 author errata, `getz-hahn-2024-errata-2026-10`, contains no
Appendix B correction. In the source, `K` is the stabilizer of a special point
in the norm-one group `G(F)¹`. The source gets its maximality from maximal
boundedness (Kaletha–Prasad, Theorem 4.2.15(1)) and openness of maximal
compact subgroups. It gets the product `P₀(F) K = G(F)` from Kaletha–Prasad,
Theorem 5.3.4 through the parahoric `P_x ≤ K`.

The implementation differs from Getz–Hahn in two places. Maximality among
compact subgroups is proved directly, by the fixed point of a compact
overgroup in the complete nonpositively curved building. This is the
fixed-point argument of the proof of Kaletha–Prasad, Theorem 4.2.15(1).
Getz–Hahn pass from the minimal parabolic only to standard parabolics. Here
every actual rational parabolic is reached, as in the proof of Kaletha–Prasad,
Theorem 5.3.4: containment of a minimal parabolic and rational conjugacy of
minimal parabolics. The minimal product of that proof is reproved in the
same way, from the chamber decomposition of Kaletha–Prasad, Theorem 5.3.3 and
Weyl representatives in the special parahoric. The Levi-intersection clause
(B.2) and the maximality of `M(F) ∩ K` in Theorem B.4.3 are not part of the
target and are not proved here.

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023): Theorem 4.2.15(1),
printed pp.173–174; Theorem 5.3.3, printed pp.189–190; Theorem 5.3.4, printed
pp.190–191 (PDF pp.221–222). Registered
source: `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`, read with
the authors' 1 November 2024 *Corrections and additions*,
`kaletha-prasad-2024-corrections`.

## Declarations

In namespace `Langlands.Global.FinitePlaceGroupPoints`:

- `parabolicIwasawaStatement : ParabolicIwasawaStatement.{u}`, the closing
  theorem.
- `ConstructionReduction.localExistence`, the local existence theorem for
  every nonarchimedean local field and connected reductive group.
- `ConstructionReduction.localExistence_of_witnesses`, the same conclusion
  from supplied parahoric building data, a realization, an apartment splitting
  and the eight axioms.

The other declarations of the module are private.

## Verification

A Lake build of the module reports no errors or warnings. The declaration
check of `parabolicIwasawaStatement` reports only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
