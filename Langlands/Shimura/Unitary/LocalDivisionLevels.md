# The maximal compact subgroup and principal congruence subgroups of a local division algebra

Author: Worker 19.

This module constructs, for a finite-dimensional division algebra `D` over a
nonarchimedean local field `k`, the compact open subgroups of `Dˣ` that
Harris uses as `p`-adic levels: the unit group `C_v = O_Dˣ` of the integer
ring, which is the unique maximal compact subgroup, and the principal
congruence subgroups `C_v^{N,0} = 1 + ϖ^N O_D`. It works with the published
normalized determinant norm of `Langlands.Algebra.DivisionAlgebraNorm`.

## Source

Harris (1997), Section 2, printed p. 88 (PDF p. 14), for the local division
algebra `B` at the distinguished place over the local field `F`: "Let
`𝒪_{B^opp}` be the maximal order in `B^opp` and let `m_v` denote the maximal
ideal of the ring `O_F` of integers in `F`. Let `C_v = 𝒪_{B^opp}ˣ`, viewed as
a maximal compact subgroup of `G`, and for any integer `N ≥ 1`, let
`C_v^{N,0} = 1 + (m_v)^N 𝒪_{B^opp} ⊂ C_v`." Printed p. 89 (PDF p. 15): "For
`j > 1`, we let `C_v^(j)` denote the (unique) maximal compact subgroup of
`GG(K_1^(j))`, and let `C(N)_p = C_v^{N,0} × ∏_{j>1} C_v^(j) × ℤ_pˣ`". These
are the levels of Harris (1998), Appendix, (A.2), and Harris (1999), (4.1)
and `K(N)_p` on printed p. 309.

As subsets of the underlying set of `B`, the integer ring of `B^opp` and its
units coincide with those of `B`; this module works with `D` itself.

## Setting

In namespace `Langlands.Shimura.LocalDivision`: `k` is a nontrivially normed
field with `CompleteSpace k` and `IsUltrametricDist k`; `D` is a division ring
with `Algebra k D` and `FiniteDimensional k D` (independent universes).
`|x|` denotes the published `Langlands.CentralDivision.regularAbsoluteValue k D x`,
the `[D : k]`-th root of `‖Algebra.norm k x‖`: multiplicative, nonarchimedean,
and equal to `‖a‖` on scalars (`regularAbsoluteValue_algebraMap`).

## Algebraic declarations

- `integerRing k D : Subring D` is `O_D = {x | |x| ≤ 1}`. Closure under
  multiplication uses multiplicativity, under addition the nonarchimedean
  inequality `regularAbsoluteValue_add_le`. `mem_integerRing` unfolds
  membership.
- `regularAbsoluteValue_eq_one_of_sub_one_lt`: `|g - 1| < 1` implies `|g| = 1`
  (two applications of the nonarchimedean inequality).
- `congruenceSubgroup k D r hr0 hr : Subgroup Dˣ`, for `0 ≤ r < 1`, is
  `{g | |g - 1| ≤ r}`. It is closed under products since
  `gh - 1 = (g - 1)h + (h - 1)` and `|h| = 1`, and under inverses since
  `g⁻¹ - 1 = -g⁻¹(g - 1)` and `|g⁻¹| = 1`. `mem_congruenceSubgroup` unfolds
  membership; `congruenceSubgroup_le_units`: it lies in `O_Dˣ` (the units of
  `integerRing`).
- `mem_congruenceSubgroup_iff_exists`: for `ϖ ≠ 0` in `k` and `N` with
  `‖ϖ‖^N < 1`, a unit `g` lies in the congruence subgroup of radius `‖ϖ‖^N`
  exactly when `g = 1 + ϖ^N y` for some `y ∈ O_D`. For a uniformizer `ϖ` of
  `k` (a generator of `m_v`), this is Harris's `C_v^{N,0} = 1 + (m_v)^N O_D`;
  the subgroup depends only on `‖ϖ‖`, hence not on the choice of uniformizer.

## Topology

- `isUltrametricDist_regular`, `isModuleTopology_regular`: with the normed
  ring structure `regularNormedRing k D` (and `regularNormedAlgebra`), `D` is
  ultrametric and carries the `k`-module topology (Mathlib's
  `isModuleTopologyOfFiniteDimensional`).
- `isOpen_integerRing_regular`, `isCompact_integerRing_regular`: in that
  normed topology `O_D` is the closed unit ball, open because the metric is
  ultrametric (`IsUltrametricDist.isOpen_closedBall`), and compact when `k` is
  locally compact (`FiniteDimensional.proper`).
- `regularTopology k D` is the topology of the regular norm.

Now give `D` a topology with `IsModuleTopology k D`:

- `topology_eq_regular`: this topology is `regularTopology k D` (both are the
  module topology).
- `isOpen_integerRing`, `isCompact_integerRing` (for `k` locally compact),
  `t2Space_of_isModuleTopology`, `continuous_regularAbsoluteValue`,
  `isClosed_congruenceBall` and `isOpen_congruenceBall` (for `r > 0`) transfer
  the corresponding normed statements.

Assume moreover `LocallyCompactSpace k`.

- `maximalCompactLevel k D : CompactOpenLevel Dˣ` is `O_Dˣ` (Harris's `C_v`
  and `C_v^(j)`): open since `O_D` is open and the value and inverse maps of
  units are continuous, compact by Mathlib's `Submonoid.units_isCompact`.
  `mem_maximalCompactLevel`: `g ∈ O_Dˣ` iff `|g| ≤ 1` and `|g⁻¹| ≤ 1`.
- `le_maximalCompactLevel_of_isCompact`: every compact subgroup `H` of `Dˣ`
  is contained in `O_Dˣ`. For `h ∈ H`, the values `|hⁿ| = |h|ⁿ` stay in the
  compact image of `H` under the continuous map `g ↦ |g|`, hence are bounded,
  so `|h| ≤ 1`; the same holds for `h⁻¹`. Thus `O_Dˣ` is the unique maximal
  compact subgroup of `Dˣ`, as in Harris's description of `C_v^(j)`.
- `congruenceLevel k D r hr0 hr : CompactOpenLevel Dˣ`, for `0 < r < 1`, is
  `congruenceSubgroup`: open as the preimage of an open ultrametric closed
  ball, compact as a closed subset of `O_Dˣ`.
  `congruenceLevel_le_maximalCompactLevel`: it is contained in `O_Dˣ`.

## Scope

`O_D` is defined as the closed unit ball of the regular norm. That it is the
unique maximal `O_k`-order of `D` (and equals the integral closure of `O_k` in
`D`) is the standard description of Harris's "maximal order" but is not
proved here; what is proved is that its unit group is the unique maximal
compact subgroup of `Dˣ`. The uniformizer `ϖ` is an input. No reduced norm
normalization, residue algebra, or invariant of `D` is used; `D` need not be
central over `k`.

## Provenance

Derived from Harris (1997), Section 2, printed pp. 88-89, read in the
original (the separately registered erratum concerns printed p. 101 and does
not affect these definitions). The description of the integer ring through the
published normalized determinant norm and the topological arguments are
implementation choices.

Source ID and SHA-256 fingerprint:

- `harris-1997-drinfeld-cohomology`:
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.

Formal dependencies: the published `Langlands.Algebra.DivisionAlgebraNorm`
(`regularAbsoluteValue`, `regularNormedRing`, `regularNormedAlgebra`), the
published `Langlands.Shimura.Levels` (`CompactOpenLevel`), and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in particular
`isModuleTopologyOfFiniteDimensional`, `eq_moduleTopology`,
`FiniteDimensional.proper`, `IsUltrametricDist.isOpen_closedBall`,
`IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm`,
`Submonoid.units_isCompact`, `IsCompact.of_isClosed_subset` and
`pow_unbounded_of_one_lt`.
