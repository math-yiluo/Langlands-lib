# A compatible maximal compact subgroup for the actual Siegel setup

Author: Worker 4149.

This module states that every actual algebraic Siegel setup admits a maximal compact
subgroup `K` of `G(𝔸_F)` with the Iwasawa property for the canonical minimal parabolic and
with the positive-torus compatibility required by
`AdelicGoodSiegelReductionStatement`. It proves this statement from three published local
Iwasawa existence statements, which are themselves unproved. No reduction-theory assertion
is made.

## The statement

`AdelicSiegelFactors.AdelicCompatibleIwasawaCompactStatement` is a definition returning
`Prop`, in universe `u`. It quantifies over every number field `F : Type u` and every group
scheme `G` over `Spec F` with `IsAffineHom G.X.hom`, `LocallyOfFiniteType G.X.hom` and
`IsConnectedReductive G` (the binders and instance arguments of
`AdelicGoodSiegelReductionStatement`), and over every `T, i, ν, T₀, j` with
`IsSiegelAlgebraicSetup F G T i ν T₀ j`. Write `P = Standard.parabolicScheme i ν ∅` with
inclusion `Standard.parabolicHom i ν ∅`. The statement asserts that there is a subgroup
`K` of `AdelicGroupPoints F G` such that

- `IsParabolicIwasawaCompact F G P (Standard.parabolicHom i ν ∅) K`: `K` is compact, every
  compact subgroup of `G(𝔸_F)` containing `K` equals `K`, and `P(𝔸_F) K = G(𝔸_F)` with the
  parabolic factor on the left;
- `IsPositiveTorusCompatible F G T i ν T₀ j K`: every `k ∈ K` in the image of `P(𝔸_F)`
  commutes with `positiveMap F G T i T₀ j a` for every `a` in the intrinsic positive
  torus `A_{T₀}`.

Both predicates are the unchanged Library predicates (modules
`Langlands.Global.AdelicIwasawaStatement` and `Langlands.Global.AdelicSiegelFiniteVolume`).
These are exactly the two conditions on the compact subgroup in
`AdelicGoodSiegelReductionStatement`.

*Provenance (derived).* Mœglin–Waldspurger (1995), I.1.4, printed p.4: for a connected
reductive group `G` over a global field with a fixed minimal parabolic `P₀` and Levi `M₀`,
the maximal compact subgroup `K = ∏_v K_v` of I.1.1 (printed p.1) can be chosen so that
"(i) `G(𝔸) = P₀(𝔸)K`; (ii) for every standard parabolic subgroup `P = MU` of `G`, the
equality `P(𝔸) ∩ K = (M(𝔸) ∩ K)(U(𝔸) ∩ K)` is satisfied, and `M(𝔸) ∩ K` is still a
compact maximal subgroup of `M(𝔸)`." Here `P₀` is the canonical minimal parabolic `P` of
the setup, and (i) together with maximality is `IsParabolicIwasawaCompact`, which is also
Getz–Hahn (2024) Theorem 2.7.1 for `P`. Compatibility is the consequence of (ii) for `P₀`
derived in the paragraph **Compatibility** of `AdelicSiegelFiniteVolume.md`: the Levi
factor of `k` commutes with `A_{T₀}` because the minimal Levi centralizes the maximal split
torus, and the unipotent factor is trivial at the archimedean places, where `A_{T₀}` is
concentrated. The statement records only these consequences, not (ii) for other standard
parabolics.

## Proved results

### `IsLeviCompatibleLocalCompact`

For a parabolic `p : P ⟶ G` and `l : M ⟶ P`, this is the local condition on a subgroup `L`
of the completion points `PlaceGroupPoints F G v` at a place `v`. At an infinite place `w`
it is the published `InfinitePlaceGroupPoints.IsLeviCompatibleIwasawaCompact F G P p M l w L`
(maximal compact, `P(F_w) L = G(F_w)`, `P(F_w) ∩ L = M(F_w) ∩ L`, and the pullback of `L`
to `M(F_w)` maximal compact). At a finite place it is
`CoordinateCompactPatching.IsLocalIwasawaCompact` (compact, maximal among compact
subgroups, and `P(F_v) L = G(F_v)`). `IsLeviCompatibleLocalCompact.isLocalIwasawaCompact`
proves that the condition always implies `IsLocalIwasawaCompact` at its place, by dropping
the last two clauses at infinite places.

### `exists_leviCompatible_parabolicIwasawaCompact`

Assume that `G` and `P` are affine schemes, and assume a Levi-compatible Iwasawa compact at every infinite place, a
local Iwasawa compact at every finite place, and an integral Iwasawa family `K₀`
(`IntegralIwasawaFamily.IsIntegralIwasawaFamily F G P p K₀`). Then there is a local family
`Kloc` whose infinite-place members are Levi-compatible Iwasawa compacts and whose
coordinate subgroup
`CoordinateCompactAssembly.coordinateSubgroup (fun v => atPlace F G v) Kloc`
(the adelic points all of whose local components lie in `Kloc v`) satisfies
`IsParabolicIwasawaCompact F G P p`.

*Proof.* This is the published argument of
`AdelicGroupPoints.exists_parabolicIwasawaCompact_of_local_integral`, with a stronger
local condition. Extend `K₀` to all places by `⊤` at the infinite places
(`extendFinite`) and repair it with `CoordinateCompactPatching.patchFamily` for the
condition `IsLeviCompatibleLocalCompact`: a member is kept if it satisfies the condition
and is otherwise replaced by a chosen member that does. By `patchFamily_eventually_eq`
and `eventually_place_of_finite`, the repaired family `Kloc` agrees with the extension at
all but finitely many places, because `K₀` is a local Iwasawa compact at almost every
finite place. Hence `Kloc` is still uniformly integral (`IsUniformlyIntegral.of_eventuallyEq`),
which gives a continuous lift of its product, and every adelic point has almost all local
components in `Kloc` (`eventually_atPlace_mem_of_finite`). The published
`CoordinateCompactAssembly.compact_maximal_coordinateSubgroup` then gives compactness and
maximality of the coordinate subgroup, and
`CoordinateCompactAssembly.range_mul_coordinateSubgroup_eq_univ` gives
`P(𝔸_F) K = G(𝔸_F)`, using `atPlace_map` and `exists_atPlace_eq_of_eventually_one`.

### `adelicCompatibleIwasawaCompactStatement_of_local`

The three published statements

- `InfinitePlaceGroupPoints.LeviCompatibleIwasawaStatement` (archimedean Iwasawa
  existence compatible with a rational Levi; proof task
  `cff6372d-c8c5-4401-ba0b-dc531bbe0b01`),
- `FinitePlaceGroupPoints.ParabolicIwasawaStatement` (finite-place Iwasawa existence; proof
  task `c0b4e50a-0d4b-4247-8801-5eb445e19645`),
- `IntegralIwasawaFamily.ExistenceStatement` (an almost-everywhere integral Iwasawa family;
  proof task `74d01809-55d8-4867-8ffe-20dc556d7370`)

imply `AdelicCompatibleIwasawaCompactStatement` in the same universe.

*Proof.* Fix the data and the setup. The setup's minimal parabolic clause gives
`IsParabolicSubgroup (Standard.parabolicHom i ν ∅)`
(`IsMinimalParabolicSubgroup.isParabolicSubgroup`), and its rational Levi clause gives
`IsRationalLeviSubgroup (Standard.leviToParabolic i ν ∅)`. `G` is affine because its
structure map is affine, and the canonical parabolic is affine as a closed subgroup. Apply
the three statements to the canonical parabolic and Levi, and then the previous theorem.
This yields `Kloc` with Levi-compatible archimedean members and an Iwasawa coordinate
subgroup `K`. The published `isPositiveTorusCompatible_coordinateSubgroup` (module
`Langlands.Global.AdelicPositiveTorusCompatibility`) proves that this coordinate subgroup
is `IsPositiveTorusCompatible` for the setup. Its proof is the derivation recalled above:
the positive image has trivial finite components, and at an infinite place a parabolic
element of the local compact lies in the Levi, which centralizes the torus.

## Use

Together with `SiegelAlgebraicSetupExistenceStatement` and a coverage statement keeping a
supplied Iwasawa compact subgroup (such as `exists_isSiegelCover_of_chamber`), this
statement gives `AdelicGoodSiegelReductionStatement`. That composition is left to the
final proof of task `6adbbc46-4bb2-4c01-843a-d8ded48189f2`.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series*,
  Cambridge University Press, 1995, registered as
  `moeglin-waldspurger-1995-spectral-decomposition` (folder SHA-256
  `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`). Chapter file
  `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, PDF pp.1–4: I.1.1 (choice of
  `K = ∏_v K_v`, printed p.1) and I.1.4 (conditions (i)–(ii), printed p.4).
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, 2024,
  registered as `getz-hahn-2024-automorphic-representations` (SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`), §2.7, printed p.71
  (PDF p.88): Theorem 2.7.1 and the choice of `K` before (2.25).
