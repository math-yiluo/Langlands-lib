# Rational root points fixing path weight lines

This module is an internal prerequisite for the even type `A` case of the
quasi-split Steinberg quotient task (Steinberg 1965, §9.10–9.19). In Steinberg's
substitute product `N'' = X_α σ_α ∏_{j ≠ m, m+1} X_j σ_j` for type `A_{2m}`, the
middle basis vector of the standard representation is fixed by every factor. So
`N''` lies in the hypersurface `f = 0`, where `f = det(1 - ·)`. This module proves the
factor-level statements for the representation of
`Rational.PathFundamentalWeights` for the reflection representatives. Rational
points of root subgroups, and the canonical reflection representatives built from
them, fix every vector of each path weight line that their roots do not move. No
basis normalization or explicit scalar is needed.

## Setting

The stabilizer definition is in `Langlands.GroupScheme.MatrixRepresentation`, for an
actual matrix representation `ρ` of a group scheme `G` over an arbitrary field
`k`. Rational points are the Library's `rationalPoints G`. The additive-group
lemma is in `MatrixRepresentation.AdditiveDividedPowers`. The remaining
results are in `Langlands.GroupScheme.SplitPinning`, with a supplied split pinning
`p` of an actual affine group scheme `G`. They use the path notions `IsPathComponent β`,
`IsPathFundamental β lam` and `pathWeight` of
`Langlands.LinearAlgebra.RootDatumPathWeights`. They also assume
`hρ : p.IsHighestWeight ρ lam`. `V_j` denotes
`p.representationWeightSpace ρ (pathWeight β lam j)`.

## Definition

`MatrixRepresentation.rationalStabilizer ρ v` is the subgroup of
`rationalPoints G` consisting of the rational points `g` with
`ρ.rationalMatrix g *ᵥ v = v`. It is a subgroup because `rationalMatrix` is a
monoid homomorphism into `GL n k`. `mem_rationalStabilizer` unfolds membership.

## Results

- `AdditiveDividedPowers.rationalMatrix_mulVec_eq_self`: let `σ` be an actual matrix
  representation of the one-dimensional vector group, and suppose
  `dividedPower σ m v = 0` for every `m ≥ 1`. Then every rational point of the
  vector group fixes `v`.
- `rationalMatrix_mulVec_eq_self_of_isRepresentedBy`: let `F.IsRepresentedBy y` for a
  subgroup functor `F` and an additive map `y`, and suppose every positive divided
  power of `ρ.restrict y` kills `v`. Then every rational point in
  `F.carrier (Over.mk (𝟙 _))` fixes `v`.
- `rationalMatrix_mulVec_eq_self_of_mem_rootSup`: let `r` be any root index. Suppose
  no positive multiple of `α_r`, and none of `-α_r`, moves `ε_j` to a path
  weight. Then every rational point in the supremum of the rational root subgroups
  of `α_r` and `-α_r` fixes every `v ∈ V_j`.
- `root_path_eq_sub`: the root of the path vertex `β i` is `ε_i - ε_{i+1}`.
- `canonicalReflection_path_fixes`: for a path vertex `β t` and any normalized
  parametrization `x` of its root, the canonical representative
  `x.reflectionRepresentative` fixes every `v ∈ V_j` with `j ≤ L`,
  `j ≠ t` and `j ≠ t + 1`.
- `canonicalReflection_offPath_fixes`: for a simple root `z` off the path and any
  normalized parametrization `x` of its root, `x.reflectionRepresentative` fixes
  every vector of every path line.
- `rootSup_pathRoot_fixes`: let `r` be a root with `α_r = ε_i - ε_l`
  (`i < l ≤ L`), for example Steinberg's merged root `α_m + α_{m+1}`. Then every
  rational point in the supremum of the rational root subgroups of `± α_r` fixes
  every `v ∈ V_j` with `j ≤ L`, `j ≠ i` and `j ≠ l`.

## Proof as implemented

**Additive group.** Write a rational point `g` of the vector group as
`scalarPoint c` (`VectorGroup.scalarPoint_coordinate`). Its constant point over
the affine test `Spec k` is the affine point with the corresponding coordinate
`c' ∈ k`. This uses `VectorGroup.scalarPoint_comp` and
`VectorGroup.affinePoint_eq_scalarPoint`. The published
`affineMatrix_constantPoint` identifies the matrix there with the rational
matrix, and the published `affineMatrix_mulVec_eq_sum` expands the action as
`Σ_m c'^m D_m v`. Only `D_0 v = v` survives.

**Represented subgroups.** By `IsRepresentedBy` and `SubgroupFunctor.mem_range`,
such a rational point is `w ≫ y` for a rational point `w` of the vector group.
`rationalMatrix_restrict` reduces to the additive case.

**Root subgroups.** The published `SplitPinning.nonempty_linkedRootParametrization`
gives additive maps representing the entire root subgroups of `α_r` and `-α_r`,
equivariant for `α_r` and `-α_r`. By the hypothesis on shifts,
`PathRootActions.dividedPower_eq_zero_of_shift_ne` kills `V_j` under every
positive divided power of either map. Both root subgroups therefore lie in
`rationalStabilizer ρ v`, and so does their supremum.

**Canonical representatives.** The published
`NormalizedRootParametrization.reflectionRepresentative_mem_generated` places
the canonical representative in that supremum. The shift classification of
`PathRootActions` (`pathWeight_add_nsmul_sub_eq_iff` and its primed form, and
`pathWeight_add_nsmul_root_ne` with its negative form) verifies the shift
hypotheses for the stated lines.

## Scope

The module concerns rational points only. It does not treat the parametrized factors
`x_α(s)` over general tests, products such as `N''`, the polynomial matrix of the
modified product, or the class function `f`. It also does not show that the
representatives act on the moved lines by any particular scalar. These remain
later even type `A` obligations of the host task.
