# Pattern subgroups of the adelic upper unitriangular group

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingGroups` (namespace
`Langlands.Global.CuspidalPairEisenstein.Unfolding`) works on the group
`N₀(𝔸) = RankinSelbergGlobal.unipotentAdelic F n`, the adelic points of the upper
unitriangular subgroup functor of `GL_n` over a number field `F`. This is the group over which
the Library's generic coefficients integrate. The module translates between points and
matrices and introduces the pattern subgroups `Λ_J(𝔸)`. In the two-block `GL_n` analogue of
Shahidi, *Functional equation satisfied by certain L-functions*, Compositio Math. 37 (1978),
proof of Lemma 2.1, they play the role of the stabilizers: the rational stabilizers
`γ P_F γ⁻¹ ∩ U_F` of (2.10.2), p. 181, and the group `V = wPw⁻¹ ∩ U` defined after (2.10.3),
p. 182. Shahidi works with a split group of type `G₂`, and his `U` is the unipotent radical of
a fixed Borel subgroup (§1, p. 173). For `GL_n` its counterpart is the upper unitriangular
group, here `N₀`. The source works with the right quotient `G_F/P_F`. In the Library's left
quotient `P \ G`, which corresponds to it under inversion `g ↦ g⁻¹`, these become the groups
`N₀ ∩ γ_J⁻¹ P γ_J` for the cell representatives `γ_J` of
[CuspidalPairEisensteinUnfoldingCells.md](CuspidalPairEisensteinUnfoldingCells.md).

## Points and matrices

- Global instances: `N₀(𝔸)` is locally compact and second countable
  (`unipotentAdelicLocallyCompact`, `unipotentAdelicSecondCountable`).
- `toMat F n : N₀(𝔸) →* GL_n(𝔸)` is the matrix of a point, through
  `GeneralLinearGroupPoints.adelicEquiv`. It is continuous and injective, with upper unitriangular
  values (`continuous_toMat`, `toMat_injective`, `isUnitriangular_toMat`,
  `toMat_mem_upperUnipotent`). `ofMat` is its inverse on upper unitriangular matrices, and
  `ofUnitriangular` is the continuous map from the space of unitriangular adelic matrices.
- `ratHom F n` embeds the rational upper unitriangular matrices into `N₀(𝔸)`, with
  `toMat_ratHom`. `Γ₀ F n` is the Library's rational subgroup
  `AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n)`. `mem_Γ₀_iff`:
  it is the image of `ratHom`. It is discrete (`isDiscrete_Γ₀`).

## Pattern subgroups

- `pattern F n J`: the points whose matrix lies in `RowEchelon.stabilizer J`, that is, whose
  entries from rows in `J` to columns outside `J` vanish. It is a closed subgroup
  (`isClosed_pattern`), hence locally compact and second countable.
- `patternLattice F n J`: the rational points of `pattern F n J`, a discrete subgroup of it
  (`isDiscrete_patternLattice`). `patternRational F n J = Γ₀ F n ⊓ pattern F n J` is its image
  in `N₀(𝔸)` (`mem_patternRational_iff_image`). `ratHom_mem_pattern_iff` identifies the
  rational elements of the pattern group with `RowEchelon.stabilizer J` over `F`.

## Finite covolume

- `exists_pattern_column_step` and `exists_pattern_mul_mem`: let `D ⊆ 𝔸` be a set meeting
  every coset `F + a`. Then every unitriangular adelic matrix `M` is carried, by left
  multiplication with a rational unitriangular matrix in the pattern of `J`, to a matrix whose
  entries `(i, j)` with `i < j` and not `(i ∈ J, j ∉ J)` all lie in `D`. The reduction treats
  the columns from left to right. At column `m` it adds rational multiples of row `m` to the
  rows above it, except to rows in `J` when `m ∉ J`. This leaves the earlier columns unchanged,
  because row `m` of a unitriangular matrix vanishes before column `m`.
- `exists_isCompact_pattern_cover`: with the compact `D` of
  `AdelicGroupPoints.exists_isCompact_algebraMap_add_mem`, every point of `pattern F n J` is
  carried by `patternLattice F n J` into one compact set.
- Hence `isFiniteMeasure_patternQuotient`: the Haar quotient measure on
  `Λ_J(F) \ Λ_J(𝔸)` is finite. By the Library's
  `LeftCosetSpace.isMulRightInvariant_haar_of_isFiniteMeasure`, Haar measure on
  `pattern F n J` is right invariant (`haar_pattern_isMulRightInvariant`) and inversion
  invariant (`haar_pattern_isInvInvariant`). `countable_patternLattice` records that the lattice
  is countable.

With `J = ∅` the pattern group is all of `N₀(𝔸)`, so the same cover gives a compact set meeting
every `N₀(F)`-orbit.
