# `Δ(P)`, `Δ̂(P)`, `Δ^∨(P)`, `β̌` and the chambers of Renard V.3.14–V.3.16

Worker 4, for Task 1222. Module
`Langlands.Representation.LanglandsClassification.ParabolicChamberStatements`,
namespace `Langlands.GroupScheme`.

This file states Renard V.3.14, V.3.15 and V.3.16 for a standard parabolic
subgroup `P = MN`. It defines the sets `Δ(P)`, `Δ̂(P)`, `Δ^∨(P)`, `Δ̂^∨(P)`,
the relation `β ↦ β̌`, and the cones and chambers of V.3.15–V.3.16 that the
Library does not already contain. Each object is given in two settings:

- inside `𝔞^*_∅` and `𝔞_∅`;
- on the split component `A` of `M`, so that `𝔞^*_M = Vstar A` and
  `𝔞_M = V A`.

The file proves the parts of V.3.16 that follow directly from the
definitions: the two intersection formulas, convexity, and the two cell
decompositions. It also proves some short compatibility lemmas. The remaining
assertions are the statement targets:

- `ParabolicChamberLinearAlgebraStatement`, inside `𝔞^*_∅` and `𝔞_∅`;
- `ParabolicSplitComponentChamberStatement`, on the split component;
- `ParabolicChamberStatement`, the conjunction of the two.

None of the three targets is proved here.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. These
passages were read in the original PDF:

- V.3.14, printed p.113 / PDF p.119. The book chooses `P_∅ ⊂ P` with
  `A_M ⊂ A_∅` and sets
  `Δ(P) = {α|_{𝔞_M} | α ∈ Δ_∅ ∖ Δ^M_∅}` and
  `Δ̂(P) = {ϖ_α|_{𝔞_M} | α ∈ Δ_∅ ∖ Δ^M_∅}`. It defines `Δ^∨(P)` and
  `Δ̂^∨(P)` dually. For `β = α|_{𝔞_M}` it writes `β̌` for the projection to
  `𝔞_M` of the coroot `α̌`. Two remarks follow: `β̌` is not a coroot, and
  `(𝔞^G_M)^*` is spanned by `Δ(P)`.
- V.3.15, printed p.113 / PDF p.119. The cones `⁺[𝔞^*]^G_P` (positive
  combinations of `Δ(P)`) and its closure; the chambers
  `^G_P[𝔞^*]^+ = {χ ∈ 𝔞^* | ⟨χ, β̌⟩ > 0, β ∈ Δ(P)}` and its closure (`≥ 0`).
  The `𝔞`-versions are obtained by exchanging roots and coroots, and the
  negative versions are the negatives. The remark at the end:
  `χ ∈ ^G_P[𝔞^*]^+` exactly when `χ = Σ c_α ϖ_α + μ` with `c_α > 0` and
  `μ ∈ 𝔞^*_G`, and the same with `c_α ≥ 0` for the closure.
- V.3.16, printed p.114 / PDF p.120. `^G_P[𝔞^*_M]^+` is not a strict cone,
  since it is stable under adding `𝔞^*_G`. The intersection
  `^G_P[(𝔞^G_M)^*]^+ = ^G_P[𝔞^*_M]^+ ∩ (𝔞^G_M)^* = {Σ c_α ϖ_α, c_α > 0}` is an
  open convex cone. Its closure
  `^G_P[𝔞^*_M]^+‾ ∩ (𝔞^G_M)^* = {Σ c_α ϖ_α, c_α ≥ 0}` is a closed convex cone.
  The book then gives
  `^G_P[𝔞^*_M]^+ = ^G_P[(𝔞^G_M)^*]^+ ⊕ 𝔞^*_G`, the same for the closures, and
  the cell decompositions
  `^G_P[(𝔞^G_M)^*]^+‾ = ⊔_{P ⊂ Q = LU} ^G_Q[(𝔞^G_L)^*]^+` and
  `^G_P[𝔞^*_M]^+‾ = ⊔_{P ⊂ Q = LU} ^G_Q[𝔞^*_L]^+`.

The notation and decompositions of V.3.12–V.3.13 (printed pp.112–113 /
PDF pp.118–119) come from the published module
`Langlands.GroupScheme.Rational.RelativeRealCorootStatements`.

## Setting

All definitions take a field `k`, a group scheme `G` over `Spec k` with affine
structure map, a commutative group scheme `T` with a monomorphism
`i : T.toGrp ⟶ G`, a cocharacter
`ν` and integral relative reflection data `D : RelativeRootReflectionData i`.
In the statement targets, `G` is connected reductive, `i` is a maximal split
torus and `ν` is generic. So `T` is the book's `A_∅`, `ν` determines the
minimal parabolic `P_∅` and its simple roots `simpleRelativeRoots i ν = Δ_∅`,
and `D` supplies the coroots `α̌ = D.realCoroot α = 1 ⊗ D.coroot α`.

A standard parabolic subgroup `P = MN` is encoded by its set of simple roots
`J = Δ^M_∅ ⊆ Δ_∅`, as in the published `LanglandsTriplet` and
`LanglandsDecompositionCones` modules. The book allows an arbitrary parabolic
`P` and chooses `P_∅ ⊂ P`. By V.3.9 this reduces to a standard `P`, and the
formalization works only with standard ones. Standard parabolic subgroups
`Q = LU ⊇ P` correspond to sets `K` of simple roots with `J ⊆ K ⊆ Δ_∅`.

The spaces are the published ones of `RealTorusSpace`:

| book | Lean |
| --- | --- |
| `𝔞^*_∅`, `𝔞_∅` | `Vstar T`, `V T` |
| `𝔞^*_M` (coroot orthogonal of `Δ^M_∅`) | `corootAnnihilator i D J` |
| `𝔞_M` (root orthogonal of `Δ^M_∅`) | `rootAnnihilator T J` |
| `(𝔞^G_∅)^*` | `relativeRootSpanReal i` |
| `𝔞^G_∅` | `cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i))` |
| `𝔞^*_G` | `LinearMap.range (rationalCharacterRestrictReal i)` |
| `(𝔞^G_M)^*` | `corootAnnihilator i D J ⊓ relativeRootSpanReal i` |
| `𝔞^G_M` | `rootAnnihilator T J ⊓ cocharacterAnnihilator (…)` |

The identifications of `𝔞^*_G` with the coroot annihilator of `Δ_∅`, and of
`𝔞^G_∅` with the span of the coroots, are conjuncts of the published
`StandardLeviRealDecompositionStatement`. So is the decomposition
`𝔞^*_∅ = 𝔞^*_M ⊕ span J`, which makes the projection to `𝔞^*_M` along
`span J` well defined.

For the split-component form, the statement takes:

- a closed subgroup `j : L ⟶ G` representing `standardLevi i ν J`;
- a split component `a : A.toGrp ⟶ L` (`IsSplitComponent a`);
- the factor `f : A ⟶ T` with `groupHom f ≫ i = a ≫ j`.

Restriction of real characters along `f` is
`rationalCharacterRestrictReal (CommGroupScheme.groupHom f) : Vstar T → Vstar A`.
The real cocharacter map is `cocharacterMapReal f : V A → V T`; it identifies
`V A` with `𝔞_M ⊂ 𝔞_∅`. The two maps are adjoint for the real pairings
(published `pair_cocharacterMapReal`).

## Definitions

Definitions inside `𝔞^*_∅` and `𝔞_∅`:

- `parabolicRoots i ν D J` (`Δ(P)`) is the published
  `D.projectedRoots J (Δ_∅ ∖ J)`: the projections to `𝔞^*_M` along `span J` of
  the simple roots outside `J`. Such a projection realizes `α|_{𝔞_M}` inside
  `𝔞^*_M` through the perfect pairing of `𝔞^*_M` with `𝔞_M`.
- `parabolicCoroots i ν D J` (`Δ^∨(P)`) is `D.projectedCoroots J (Δ_∅ ∖ J)`:
  the projections `β̌` to `𝔞_M`, along the span of the coroots of `J`, of the
  coroots `α̌`, `α ∈ Δ_∅ ∖ J`.
- `parabolicFundamentalWeights i ν D J` (`Δ̂(P)`) is the set of fundamental
  weights `ϖ_α` (published `IsRealFundamentalWeight`) with `α ∉ J`.
  `parabolicFundamentalWeights_subset` shows they lie in `(𝔞^G_M)^*`, so each
  is its own projection to `𝔞^*_M`.
- `parabolicFundamentalCoweights i ν J` (`Δ̂^∨(P)`) is the set of fundamental
  coweights `ϖ^∨_α` (published `IsRealFundamentalCoweight`) with `α ∉ J`.
  They lie in `𝔞^G_M` (`parabolicFundamentalCoweights_subset`).
- `IsParabolicCorootOf i ν D J y v` (the assignment `β ↦ β̌`) holds when, for
  some simple root `α ∉ J`, `y` is the projection of `α` and `v` the
  projection of `α̌`.
- `closedSimpleCorootFace i ν D J` (closure of `^G_P[𝔞^*_M]^+`) is the set of
  `y` with `⟨y, α̌⟩ = 0` for the roots `α ∈ J` and `⟨y, α̌⟩ ≥ 0` for the simple
  roots `α ∉ J`. The open chamber `^G_P[𝔞^*_M]^+` is the published
  `openSimpleCorootFace i ν D J`, which has `> 0` instead. The first condition
  says `y ∈ 𝔞^*_M`. On `𝔞^*_M`, pairing with `α̌` equals pairing with its
  projection `β̌` (`pair_eq_of_mem_projectedCoroots`). So these are the book's
  conditions `⟨χ, β̌⟩ > 0` (resp. `≥ 0`).
- `projectedRootPositiveCone i D J S` (`⁺[𝔞^*_M]^G_P` for `S = Δ_∅ ∖ J`) is
  the set of `y ∈ 𝔞^*_M` congruent modulo `span J` to `Σ_{α ∈ S} c_α α` with
  every `c_α > 0`. The definition asks for a finset with underlying set `S`,
  so the set is empty for infinite `S`. The closure is the published
  `projectedRootNonnegCone i D J S`.
- `projectedCorootPositiveCone i D J S` (`⁺[𝔞_M]^G_P`) and
  `projectedCorootNonnegCone i D J S` (its closure) are the same constructions
  with coroots in place of roots. They are the positive (resp. nonnegative)
  combinations of the `β̌`.
- `openCorootFaceCone i ν D J : ConvexCone ℝ (Vstar T)` and
  `closedCorootFaceCone i ν D J : PointedCone ℝ (Vstar T)` are the published
  sets `openCorootFace i ν D J` (`^G_P[(𝔞^G_M)^*]^+`) and
  `closedCorootFace i ν D J` (its closure), with the cone axioms proved.

Definitions on the split component (`𝔞^*_M = Vstar A`, `𝔞_M = V A`):

- `restrictedFundamentalWeights i ν D J f` (`Δ̂(P)`): the restrictions along
  `f` of the `ϖ_α`, `α ∉ J`. This is the book's definition
  `ϖ_α|_{𝔞_M}` verbatim.
- `restrictedParabolicCoroots i ν D J f` (`Δ^∨(P)`): the preimage under
  `cocharacterMapReal f` of `parabolicCoroots i ν D J`.
- `restrictedFundamentalCoweights i ν J f` (`Δ̂^∨(P)`): the preimage of
  `parabolicFundamentalCoweights i ν J`.
- `IsRestrictedParabolicCoroot i ν D J f β v` (`v = β̌`): for some simple root
  `α ∉ J`, `β = α|_{𝔞_M}` (`restrictedRootVector f α = β`) and the image of
  `v` in `𝔞_∅` is the projection of `α̌`. `mem_restrictedParabolicCoroots`
  shows that `Δ^∨(P)` is the set of all such `v`.
- `parabolicCorootChamber i ν D J f` and
  `parabolicClosedCorootChamber i ν D J f` are V.3.15 as printed:
  `{χ ∈ Vstar A | ⟨χ, β̌⟩ > 0}` (resp. `≥ 0`), quantified over all pairs `(β, β̌)`
  related by `IsRestrictedParabolicCoroot`. The published
  `restrictedCorootChamber` and `restrictedClosedCorootChamber` of
  `LanglandsTriplet` define these chambers differently, by lifting to `𝔞^*_∅`.
  The statement asserts that the two definitions agree.
- `restrictedCorootPositiveCone i ν D J f` and
  `restrictedCorootNonnegCone i ν D J f` (`⁺[𝔞]^G_P` and its closure): the
  preimages of `projectedCorootPositiveCone i D J (Δ_∅ ∖ J)` and
  `projectedCorootNonnegCone i D J (Δ_∅ ∖ J)`.

The root-side cones `⁺[𝔞^*]^G_P` on `Vstar A` already exist as the published
`restrictedRootPositiveCone` and `restrictedRootNonnegCone`. `Δ(P)` on `Vstar A`
is the published `restrictedSimpleRoots i ν J f`. Neither is redefined here.
The negative versions `⁻[𝔞]^G_P` and `^G_P[𝔞]^-` of V.3.15 are the pointwise
negatives `-S` of these sets and get no separate names. The `𝔞`-chambers
`^G_P[𝔞]^+` and their closures on `V A` are not redefined here. They are
`chamber` and `closedChamber` in the module
`Langlands.BruhatTits.Cartan.RenardLeviCones` (Worker 4's accepted candidate
`089ffdc0`). This file does not import that module.

## Proved results

These lemmas are proved here and are not part of the statement targets:

- `parabolicFundamentalWeights_subset` and
  `parabolicFundamentalCoweights_subset`: for `J ⊆ Δ_∅`, `Δ̂(P) ⊆ (𝔞^G_M)^*`
  and `Δ̂^∨(P) ⊆ 𝔞^G_M`. The proofs use the vanishing conditions of the
  fundamental (co)weights at the other simple (co)roots.
- `pair_eq_of_mem_projectedCoroots` and `pair_eq_of_mem_projectedRoots`: on
  `𝔞^*_M`, pairing with a projected coroot equals pairing with the coroot. On
  `𝔞_M`, pairing with a projected root equals evaluating the root. The
  difference lies in a span that pairs to zero.
- `pair_pos_of_mem_openSimpleCorootFace`: points of `^G_P[𝔞^*_M]^+` are
  positive on every `β̌`.
- `openCorootFace_subset`, `closedCorootFace_subset`: both faces lie in
  `(𝔞^G_M)^*`.
- `openCorootFace_eq_inter` and `closedCorootFace_eq_inter` (V.3.16, first two
  displays):
  `^G_P[(𝔞^G_M)^*]^+ = ^G_P[𝔞^*_M]^+ ∩ (𝔞^G_∅)^*`, and the same for the
  closures. The faces already lie in `𝔞^*_M`, so intersecting with
  `(𝔞^G_∅)^*` is intersecting with `(𝔞^G_M)^*`.
- `openSimpleCorootFace_subset_closed`, `openCorootFace_subset_closed`,
  `convex_openCorootFace`, `convex_closedCorootFace`.
- `closedCorootFace_eq_iUnion` and `pairwiseDisjoint_openCorootFace`
  (V.3.16, first cell decomposition): for `J ⊆ Δ_∅`, the closed face of `J` is
  the union over `J ⊆ K ⊆ Δ_∅` of the open faces of `K`. The open faces of
  distinct `K ⊆ Δ_∅` are disjoint.
- `closedSimpleCorootFace_eq_iUnion` and
  `pairwiseDisjoint_openSimpleCorootFace` (V.3.16, second cell decomposition):
  the same for the chambers `^G_Q[𝔞^*_L]^+`.
- `mem_restrictedParabolicCoroots` (see above).
- `pair_restrictedRootVector_of_isRealFundamentalCoweight`: if the image of
  `w ∈ V A` is `ϖ^∨_α`, then `⟨α'|_{𝔞_M}, w⟩` is `1` for `α' = α` and `0` for
  the other simple roots. So `Δ̂^∨(P)` is dual to `Δ(P)`.
- `pair_restrict_of_isRealFundamentalWeight`: for `α ∉ J`, if the image of
  `v ∈ V A` is the projection of the coroot of a simple root `α'`, then
  `⟨ϖ_α|_{𝔞_M}, v⟩` is `1` for `α' = α` and `0` otherwise. So `Δ̂(P)` is dual
  to `Δ^∨(P)`.

The cell decompositions come from two private combinatorial lemmas about
generic cells. `openCell e q Z Δ K` is the set of points of `Z` where `q a`
vanishes for `e a ∈ K` and is positive for `e a ∈ Δ ∖ K`. `closedCell` is the
same with `≥ 0` in place of `> 0`. A point `y` of the closed cell of `J`
belongs to the open cell of `K = J ∪ {χ ∈ Δ | q a y = 0 whenever e a = χ}`.
This uses injectivity of `e`, here `Subtype.val` on the relative roots. Two
open cells containing the same point have equal indices, because every index
lies in `Δ ⊆ range e`. The published faces are these cells up to `simp`, with
`Z = (𝔞^G_∅)^*` for the faces and `Z = 𝔞^*_∅` for the chambers. For the
chambers with `J = ∅`, the two lemmas recover the published
`existsUnique_openFace_of_dominant`: every dominant character lies in exactly
one open chamber.

## Statement targets

`ParabolicChamberLinearAlgebraStatement` quantifies over:

- a field `k`;
- a connected reductive `G` with maximal split torus `i : T.toGrp ⟶ G`;
- a generic cocharacter `ν` and reflection data `D`;
- a set `J ⊆ Δ_∅`.

It asserts, in order:

1. (V.3.14) every simple root `α ∉ J` has exactly one projection to `𝔞^*_M`,
   and its coroot exactly one projection to `𝔞_M`;
2. (V.3.14) distinct simple roots outside `J` have no common projection, so
   `β ↦ β̌` is well defined on `Δ(P)`;
3. (V.3.14–V.3.16) there is a basis `b` of `(𝔞^G_M)^*`, indexed by the simple
   roots outside `J`, consisting of fundamental weights. In this basis:
   - `^G_P[(𝔞^G_M)^*]^+ = {Σ c_α ϖ_α, c_α > 0}` and its closure is
     `{Σ c_α ϖ_α, c_α ≥ 0}` (V.3.16);
   - `^G_P[𝔞^*_M]^+ = {Σ c_α ϖ_α + μ, c_α > 0, μ ∈ 𝔞^*_G}`, and the same with
     `c_α ≥ 0` for the closure (the remark of V.3.15).

   The sums are `finsum` over the finite index type;
4. there is a basis of `𝔞^G_M`, indexed the same way, consisting of
   fundamental coweights (`Δ̂^∨(P)` is a basis);
5. (V.3.15) `^G_P[𝔞^*_M]^+` is the set of `y ∈ 𝔞^*_M` with `⟨y, v⟩ > 0` for
   every pair `(y', v)` with `IsParabolicCorootOf`, i.e. for every `β̌`;
6. the same for the closure with `≥ 0`;
7. (V.3.16) `^G_P[𝔞^*_M]^+ = ^G_P[(𝔞^G_M)^*]^+ + 𝔞^*_G` as a pointwise sum
   of sets;
8. the same for the closures. The sums are direct because
   `(𝔞^G_∅)^* ∩ 𝔞^*_G = 0` (published `RelativeCharacterRootComplementStatement`,
   proved as `relativeCharacterRootComplement`);
9. (V.3.16) give `Vstar T` its module topology (`moduleTopology ℝ`, the
   canonical topology of a finite-dimensional real space). Then
   `^G_P[(𝔞^G_M)^*]^+` is open in `(𝔞^G_M)^*` with the subspace topology, and
   its closure in `𝔞^*_∅` is the closed face.

The book also calls the open cone convex and the closed cone a closed convex
cone. Convexity is proved here (`convex_openCorootFace`,
`convex_closedCorootFace`, and the cone structures). Closedness follows from
item 9.

`ParabolicSplitComponentChamberStatement` takes the same data plus `L`, `j`,
`A`, `a`, `f` as in the Setting. It asserts, in order:

1. restriction along `f` maps `𝔞^*_M = corootAnnihilator i D J` bijectively
   onto `Vstar A` (`Set.BijOn … univ`);
2. restriction carries `parabolicRoots i ν D J` onto the published
   `restrictedSimpleRoots i ν J f`, which is `Δ(P)` on `Vstar A`;
3. distinct simple roots outside `J` have distinct restrictions;
4. every `β ∈ Δ(P)` has exactly one `β̌ ∈ V A`;
5. every fundamental coweight `ϖ^∨_α`, `α ∉ J`, is the image of exactly one
   vector of `V A`. So `Δ̂^∨(P) ⊂ V A` has one element for each such `α`;
6. the printed chambers equal the published lifted ones:
   `parabolicCorootChamber = restrictedCorootChamber`;
7. the same for the closed chambers:
   `parabolicClosedCorootChamber = restrictedClosedCorootChamber`;
8. (the remark of V.3.15 on `Vstar A`) `^G_P[𝔞^*]^+` is the set of
   restrictions of `Σ c_α ϖ_α + μ` with `c_α > 0` and `μ ∈ 𝔞^*_G`. By
   linearity, these are the elements `Σ c_α ϖ_α|_{𝔞_M} + μ|_{𝔞_M}`;
9. the same for the closure with `c_α ≥ 0`;
10. `⁺[𝔞]^G_P = {Σ_{α ∈ Δ_∅∖J} c_α β̌_α, c_α > 0}` on `V A`;
11. the same for the closure with `c_α ≥ 0`;
12. for `Δ_∅` finite (the hypothesis of the published cones), restriction
    carries `projectedRootPositiveCone i D J (Δ_∅ ∖ J)` onto the published
    `restrictedRootPositiveCone i ν J f hfin`;
13. the same for `projectedRootNonnegCone` and `restrictedRootNonnegCone`.

So the ambient realizations agree with the book's restricted objects.

## Remarks and choices

- **Remarks not formalized.** V.3.14 remarks that `Δ(P)` is in general not
  the set of simple roots of a root system and that `β̌` is not a coroot. This
  is a negative, informal remark with no precise statement, so it is not
  formalized.
- **Already covered.** The spanning remark `(𝔞^G_M)^* = span Δ(P)` of V.3.14
  is already in the published `StandardLeviRealDecompositionStatement`, case
  `K = Δ_∅`: `leviRootSpace J Δ_∅ = span (projectedRoots J (Δ_∅ ∖ J))`, and
  `leviRootSpace J Δ_∅ = 𝔞^*_M ∩ span Δ_∅`. The dual statement for
  `𝔞^G_M = span Δ^∨(P)` is there too. Item 3 of the linear-algebra target
  gives another spanning set, the fundamental weights.
- **"Not a strict cone."** V.3.16 notes that `^G_P[𝔞^*_M]^+` is not a strict
  cone because it is stable under `+ 𝔞^*_G`. This follows from item 7 of the
  linear-algebra target and is not stated separately.
- **Disjoint unions.** The book's `⊔` in the cell decompositions is formalized
  as a union together with pairwise disjointness of the pieces. The pieces are
  indexed by all `K` with `J ⊆ K ⊆ Δ_∅`, which correspond to the standard
  parabolic subgroups `Q ⊇ P`.
- **Ambient realization.** Inside `𝔞^*_∅`, the book's restrictions
  `α|_{𝔞_M}` and `ϖ_α|_{𝔞_M}` are realized by the projections to `𝔞^*_M`.
  This is the convention of the published `LanglandsDecompositionCones`.
  Items 1, 2, 8 and 12 of the split-component target state that restriction
  along `f` matches the two pictures. The `β̌` live in `𝔞_M ⊂ 𝔞_∅` and on
  `V A` through the injective map `cocharacterMapReal f`.
- **Hypotheses of the definitions.** The definitions need no reductivity,
  maximality or genericity. Those hypotheses enter only in the statement
  targets. Several proved lemmas need `J ⊆ Δ_∅`, which they take as an
  explicit hypothesis.
- **Fundamental weights given as predicates.** The book's `ϖ_α` and `ϖ^∨_α`
  appear through the published predicates `IsRealFundamentalWeight` and
  `IsRealFundamentalCoweight`. Their existence and uniqueness are conjuncts of
  the published `RelativeFundamentalWeightStatement`. Items 3 and 4 of the
  linear-algebra target and item 8 of the split-component target quantify over
  vectors satisfying the predicates.
