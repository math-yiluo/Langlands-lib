# An exhaustion of Drinfeld's upper half space by rational domains

Author: Worker 21.

This module writes Drinfeld's upper half space `Ω` (module
`DrinfeldUpperHalfSpace`) as an increasing union of rational domains
`V_0 ⊆ V_1 ⊆ ⋯` of the closed polydiscs, each contained in the interior of the
next. Every compact subset of `Ω` lies in one `V_N`. The members form an
indexed affinoid atlas of `Ω`, and the module builds the corresponding atlas
presentation. Morphisms of atlas presentations need a monotone choice of target
chart. A chain of charts allows such choices, so this atlas is the one used for
the group action on `Ω`.

All declarations lie in `Langlands.Analytic.DrinfeldUpperHalfSpace`. The
hypotheses on `F`, `K` and `d` are those of `DrinfeldUpperHalfSpace`. From
`exists_net` on, `F` has compact closed balls (`ProperSpace F`), and the atlas
part assumes `NeZero d`.

## Original sources and derived provenance

Drinfel'd, *Coverings of p-adic symmetric regions* (1976), registered as
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`, printed
p.107 / PDF p.1: `Ω^d` is the set of points of `ℙ^{d-1}` not lying on any
`K`-rational hyperplane, and "Ω^d is a strict analytic space over K, on which
PGL(d, K) acts". The analytic structure is given in the source's reference [1].

Harris, *Galois properties of cohomological automorphic forms on GL(n)* (1999),
registered as `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
§2, printed p.303 / PDF p.5, uses the admissible covering of `Ω` by the open
sets `U(e)` and the action of `GJ` on `Ω`.

The particular exhaustion below is derived: it is not Drinfeld's covering by
the inverse images of simplices of the building. It only uses compactness of
the shell of coefficient vectors and the triangle inequality, and its purpose is
to supply a chain atlas.

## Construction

- `bigScalar F` is a fixed `c ∈ F` with `1 < ‖c‖`; it fixes the shell
  `shell F d c = {a | ‖c‖⁻¹ ≤ ‖a‖ ≤ 1}`.
- `threshold N = 4⁻ᴺ` (written `δ_N`), so `δ_{N+1} = δ_N / 4`.
- `mesh K d N = δ_N / (2 (d + 1) ‖ϖ‖⁻ᴺ)` (written `η_N`). `mesh_mul` records
  `(d + 1) η_N ‖ϖ‖⁻ᴺ = δ_N / 2`.
- `net F K d N` is a chosen finite subset of the shell such that every point of
  the shell is within `η_N` of it (`exists_net`, from compactness of the shell;
  `net_subset_shell`, `exists_mem_net`).
- `exhaustionChart F K d N` is the rational chart `laurentInter` of the `N`-th
  closed polydisc for the threshold `δ_N` and the forms `ℓ_b`, `b` in the net.
  `mem_locus_exhaustionChart`: its locus is
  `{y | δ_N ≤ |ℓ_b(y)| for all b in the net}`.
- `exhaustion F K d N` is the image `V_N` of this locus in the affine space.

Two estimates are used throughout:

- `linearForm_coefficients_ge`: on the `M`-th polydisc,
  `|ℓ_a| ≥ |ℓ_b| − (d + 1) ‖a − b‖ ‖ϖ‖⁻ᴹ`. This is subadditivity of the
  seminorm together with `linearForm_le`.
- `linearForm_ne_zero_of_smul`: if `|ℓ_{t•a}| > 0` then `|ℓ_a| ≠ 0`, because
  `ℓ_{t•a} = t ℓ_a`.

## Properties

- `exhaustion_subset_omega`: `V_N ⊆ Ω`. For `a ≠ 0` rescale to `t • a` in the
  shell and choose `b` in the net within `η_N`; then
  `|ℓ_{t•a}| ≥ δ_N − δ_N / 2 > 0`.
- `exhaustion_mem_nhds`, `exhaustion_subset_interior`: `V_{N+1}` is a
  neighborhood of every point of `V_N`. The open set of points of the open disc
  `|Tᵢ| < ‖ϖ‖⁻⁽ᴺ⁺¹⁾` where `|ℓ_b| > δ_{N+1}` for all `b` in the `(N+1)`-st net
  contains the point (each such `b` is within `η_N` of a member of the `N`-th
  net, so `|ℓ_b| ≥ δ_N / 2 > δ_N / 4`), and it lies in `V_{N+1}`.
- `exhaustion_subset_succ`, `exhaustion_mono`: the chain is increasing.
- `exists_mem_exhaustion`: every point of `Ω` lies in some `V_N`. The function
  `a ↦ |ℓ_a(z)|` is Lipschitz and positive on the compact shell, with minimum
  `δ > 0`; take `N` at least the polydisc index of `z` with `4⁻ᴺ < δ`.
- `iUnion_exhaustion`: `⋃ N, V_N = Ω`.
- `exists_subset_exhaustion`: a compact subset of `Ω` lies in some `V_N`. The
  interiors of the `V_N` form an increasing open cover.
- `exhaustion_inter`: `V_N ∩ V_{N'} = V_{min N N'}`.

## The exhaustion atlas

- `ExhaustionIndex F K d` is the type of sets occurring as some `V_N`, so
  distinct indices have distinct chart images even if some `V_N` coincide.
  `level U` is the first `N` with `V_N = U` (`exhaustion_level`), and
  `ofLevel N` is `V_N` as an index.
- `exhaustionDomain F K d N` is `V_N` as an existing `DirectedDomain` of the
  polydisc atlas `AnalyticAffineSpace.atlas K d`: the `N`-th polydisc with the
  represented domain of `exhaustionChart`. Its locus is `V_N`.
- `exhaustionChartMap F K d U` is the ambient spectrum map of
  `exhaustionDomain (level U)`, with values in `Ω`. It is continuous and
  injective (injectivity of the domain spectrum map and of the polydisc chart),
  hence a closed embedding of a compact space into the Hausdorff space `Ω`.
  `range_exhaustionChartMap` identifies its image with `U`, and
  `range_exhaustionChartMap_subset_iff` reduces chart-image inclusion to `U ⊆ V`.
- `exhaustionInclusion` is the existing `Inclusion.ofSubset` between the
  directed domains.
- `exhaustionAtlas F K d : IndexedAffinoidAtlas.{u, u, u} K (Omega F K d)`:
  - charts are `exhaustionChartMap` and algebras are the chart algebras of
    `exhaustionChart`;
  - chart images are injective in the index by construction;
  - local Hausdorffness holds since `Ω` is Hausdorff;
  - the chart family is a net. Each point of `V_N` has `V_{N+1}` as a
    neighborhood, and the intersection of two members is a member;
  - restrictions are those of `exhaustionInclusion`. The chart square is the
    existing `ambientMap_naturality`, and the universal property is the existing
    `DirectedRationalAtlas.inclusion_universal`. Identity and composition laws
    hold because inclusions of directed domains form a thin category.
- `exhaustionPresentation F K d : AffinoidAtlasPresentation.{u, u, u} K` is `Ω`
  with this atlas.

## Scope

The comparison of this presentation with `DrinfeldUpperHalfSpace.presentation`
(all rational domains of polydiscs inside `Ω`) is not proved here. The group
action, Drinfeld's affinoids `Ω_N` and the building are not treated.
