# Vanishing of a one-cell open restriction: proof

Authors: Worker 634 (relative-cell transport implementation) and Worker 1079
(production port onto the public covariance theorem and documentation).

`Langlands.Whittaker.bruhatCellRestrictionVanishing` proves the published
proposition `Langlands.Whittaker.BruhatCellRestrictionVanishingStatement.{u}`
from `Langlands.Representation.Whittaker.BruhatCellRestrictionVanishingStatement`,
unchanged. Its type is that proposition at the arbitrary universe `u`. The
proof introduces all quantifiers and premises of the statement and applies the
local theorem `RelativeCellTransport.restriction_zero_of_cellwise`, whose
hypotheses are exactly those premises.

The file is a port of Worker 634's private
`RelativeCellTransportCore` (shared draft of task
`f79ca82c-d050-4ffa-821b-c347b60e36e0`, revision 8). The only mathematical
change is that both covariance steps now apply the public theorem
`Langlands.HarmonicAnalysis.Distribution.supportedDescentCovariance`, imported
from `Langlands.HarmonicAnalysis.Distribution.SupportedDescentCovarianceProof`;
no private Core or Design module is imported. The helpers live in the
namespace `Langlands.Whittaker.RelativeCellTransport` of this proof file and
are not a separate public statement.

## Notation

Throughout, `K` is any Hausdorff topological field in universe `u`,
`G = GeneralLinear (n + 1) K`, `w` is a permutation of `Fin (n + 1)`, and

```text
ℓ(w) = permutationInversionCount (n + 1) w,
C_w  = upperBruhatCell (n + 1) K w,
L    = upperBruhatLayerLE (n + 1) K ℓ(w),
O    = upperBruhatCellNeighborhood (n + 1) K w,
P    = (Subtype.val : O → G) ⁻¹' L.
```

`P` is closed in `O` because `L` is closed (`isClosed_upperBruhatLayerLE`),
and `O` is open (`isOpen_upperBruhatCellNeighborhood`). The geometric
helpers need only the field and topology; the distribution helpers add the
statement's local compactness and total disconnectedness instances on `G`.

## Geometric helpers

- `covariance_of_conjugacy`: if homeomorphisms satisfy `b ∘ r = r ∘ a` and
  `a_* D = c • D`, then `b_* (r_* D) = c • r_* D`. The proof rewrites
  `r.trans b = a.trans r` and uses `pushforward_trans` and linearity.
- `relativeCellHomeomorph : P ≃ₜ UpperBruhatCell (n + 1) K w`. It forgets
  both subtype proofs; membership in `C_w` comes from the published identity
  `upperBruhatCellNeighborhood_inter_layer` (`O ∩ L = C_w`). The inverse
  places a cell element in `O` by the left disjunct and in `L` with witness
  `w` itself. Both inverse laws hold by `rfl`; continuity is subtype
  continuity.
- `biTranslate_mem_cell` and `biTranslate_mem_neighborhood`: for
  upper-unipotent `u₁, u₂`, `g ↦ u₁ g u₂` preserves every actual cell
  (`mul_mem_upperBruhatCell`, `mem_upperBruhatCell_mul`, applied through
  `upperUnipotentInUpperTriangular`) and hence the neighborhood `O`.
- `neighborhoodBiTranslate`: this bi-translation as a homeomorphism of `O`,
  with inverse `g ↦ u₁⁻¹ g u₂⁻¹`.
- `transpose_mem_higher`: the Weyl transpose `τ = weylTransposeHomeomorph n K`
  maps the higher-cell union `upperBruhatHigherCells (n + 1) K w` to itself.
  A point of a cell `C_v` with `ℓ(v) > ℓ(w)` goes to the cell of
  `upperBruhatTransposeIndex (n + 1) v`, which has the same inversion count
  (`permutationInversionCount_upperBruhatTransposeIndex`), by
  `weylConjugateTranspose_image_upperBruhatCell_subset`.
- `transpose_mem_neighborhood` and `neighborhoodWeylTranspose`: given the
  stability proof `hτ : Set.MapsTo τ C_w C_w`, `τ` maps `O` to itself and
  restricts to a homeomorphism of `O`, its own inverse by
  `weylTransposeHomeomorph_involutive`. These are used only with the `hτ` of
  the second branch of the cellwise alternative; no stability of arbitrary
  cells is asserted.

All restricted maps have the ambient maps as their underlying functions, so
the two inclusion-compatibility hypotheses of the covariance theorem hold by
`rfl` below.

## Descent to the actual cell

`descendToCell n K w D` is the published chosen descent
`descendInOpen (isOpen_upperBruhatCellNeighborhood w) hP D : Distribution P`,
pushed forward along `relativeCellHomeomorph`. It is a distribution on the
actual cell subtype `UpperBruhatCell (n + 1) K w`.

`biEquivariant_descendToCell` proves
`IsBiEquivariantBruhatCellDistribution n K w ψ (descendToCell n K w D)` from
global `IsBiEquivariantDistribution ψ n D`. Fix `u₁, u₂` and put
`c = standardCharacter ψ n u₁ * standardCharacter ψ n u₂` (coerced to `ℂ`).
Using `isBiEquivariantDistribution_iff`, the global premise gives
`e_* D = c • D` for the ambient bi-translation
`e = (Homeomorph.mulLeft u₁).trans (Homeomorph.mulRight u₂)`. With `b` the
published cell bi-translation `bruhatCellBiTranslate n K w u₁ u₂` and `r` the
homeomorphism above, set `eZ = r.trans (b.trans r.symm)` on `P`.
`supportedDescentCovariance`, applied with ambient map `e`, neighborhood map
`neighborhoodBiTranslate`, nested map `eZ` and scalar `c`, gives
`eZ_* (descendInOpen … D) = c • descendInOpen … D`. Since `b ∘ r = r ∘ eZ`,
`covariance_of_conjugacy` transfers this to `b_* (descendToCell D) =
c • descendToCell D`, which evaluated at each test function is the cell
bi-equivariance identity.

`antiInvariant_descendToCell` is the same argument for the restricted
transpose in the stable case. From `τ_* D = -D`, written as
`τ_* D = (-1) • D`, `supportedDescentCovariance` with ambient map `τ`,
neighborhood map `neighborhoodWeylTranspose n K w hτ` and nested map
`eZ = r.trans (b.trans r.symm)` for `b = bruhatCellWeylTranspose n K w hτ`
gives covariance with scalar `-1` on `P`; conjugacy gives
`b_* (descendToCell D) = -descendToCell D`.

`restrictOpen_zero_of_descendToCell_zero`: if `descendToCell D = 0`, then
injectivity of homeomorphism pushforward makes the `descendInOpen` term zero.
The published `closedPushforward_descendInOpen` identity writes
`restrictOpen (isOpen_upperBruhatCellNeighborhood w) D` as the closed
pushforward of that term, hence it is zero.

## Final step

`restriction_zero_of_cellwise` reduces to `descendToCell D = 0`. The descent
is bi-equivariant by `biEquivariant_descendToCell`.

1. In the first branch, every bi-equivariant distribution on the actual cell
   is zero, so the descent is zero. No transpose stability is used.
2. In the second branch, with its stability proof `hτ`, the assumed cellwise
   invariance gives `b_* (descendToCell D) = descendToCell D`, and
   `antiInvariant_descendToCell` gives `b_* (descendToCell D) =
   -descendToCell D`. Hence every value of the descent equals its own
   negative and is zero over `ℂ` (`CharZero.eq_neg_self_iff`).

The theorem `bruhatCellRestrictionVanishing` applies this result. It keeps
every hypothesis of the statement and concludes exactly
`restrictOpen (isOpen_upperBruhatCellNeighborhood w) D = 0`.

## Scope and provenance

The proof is internal deduction from the published actual Bruhat geometry
(`Langlands.Group.GL.UpperBruhatCells`,
`Langlands.Group.GL.UpperBruhatFiltrationGeometryProof`,
`Langlands.Group.GL.UpperBruhatTransposeProof`), the cell translations and
transpose of `Langlands.Representation.Whittaker.BruhatCellDistribution`, the
Whittaker distribution predicates of
`Langlands.Representation.Whittaker.Distribution`, the published supported
descent of `Langlands.HarmonicAnalysis.Distribution.SupportedRestriction`, and
the public covariance theorem. No
literature proposition is transcribed. No compatible-torus premise, Haar
measure, finite unipotent-orbit assertion or integral interchange is used.
The checked axioms are `propext`, `Classical.choice` and `Quot.sound`.

This proves only the conditional one-cell transport. The cellwise alternative
remains a premise; proving it for the relevant cells, the finite-layer
assembly, global Shalika invariance and Whittaker multiplicity one are
separate obligations.
