# Sufficiently small levels exist below every original level

Author: Worker 19.

The published module `Langlands.Shimura.Unitary.SufficientlySmallLevels` defines
Harris–Taylor's sufficiently small condition on compact-open levels of the
opposite finite-adelic similitude group `σ(A_f)ᵐᵒᵖ`. It does not prove that such
levels exist. Several published constructions over the small CM levels, such as
`exists_orderedSmallLevel_le` and the cohomology of the small-level tower, take
`Nonempty σ.SmallLevelCategory` as a hypothesis. This module proves that every
compact-open level contains a sufficiently small one. In particular, small levels
exist whenever some compact-open level does.

## Source

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), source `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`,
Chapter III.1, printed p.90 (one-based PDF p.98): "Let `U` be a sufficiently
small open compact subgroup of `G(𝔸^∞)`. By sufficiently small we shall mean
that the projection of `U` to `G(ℚ_x)` for some prime `x` contains no element of
finite order other than 1." The source uses such levels without proving that they
exist. The existence argument below is the standard one, and is implemented here.

## Setting

Declarations are in namespace `Langlands.Shimura.AlgebraInvolution`.
`σ : AlgebraInvolution ℚ A` is a rational algebra with involution, `A` finite
over `ℚ`. `σ.finiteLocalMap v` is the published continuous evaluation
`σ(A_f) → σ(ℚ_v)` at a finite place `v`, and `congruenceLevel σ v q` is the
published principal congruence level modulo `q` of `σ(ℚ_v)` (module
`Langlands.Shimura.Unitary.TorsionFreeLevels`).

## Declarations

- `oppositeCongruenceSubgroup σ v q`: the subgroup of `σ(A_f)ᵐᵒᵖ` of the
  elements `g` with `σ.pointsMap (finiteEvaluation v) (unop g)` in
  `congruenceLevel σ v q`. It is the opposite (`Subgroup.op`) of the preimage of
  the congruence level under the local evaluation. `mem_oppositeCongruenceSubgroup`
  states this membership criterion. The test is the same projection as in
  `LevelSmallAt`.
- `isOpen_oppositeCongruenceSubgroup`: for `q ≠ 0` this subgroup is open. The
  congruence level is open (`isOpen_congruenceLevel`), the local evaluation is
  continuous, and so is `MulOpposite.unop`.
- `congruenceShrink σ v hq U`: for `q ≠ 0` and a compact-open level `U`, the
  compact-open level with subgroup `U ⊓ oppositeCongruenceSubgroup σ v q`. It is
  open as an intersection of open sets. It is compact as the intersection of the
  compact set `U` with an open, hence closed, subgroup.
- `congruenceShrink_le`: the shrunk level lies in `U`.
- `levelSmallAt_congruenceShrink`: for `A` nontrivial and a prime `q ≥ 3`
  contained in `v`, the shrunk level satisfies `LevelSmallAt` at `v`. Every
  element of the shrunk level has local image in the congruence level, whose
  only element of finite order is `1` (`congruenceLevel_torsionFree`).
- `exists_levelSufficientlySmall_le`: for `A` nontrivial, every compact-open
  level `U` contains the level of some object of `σ.SmallLevelCategory`. The
  proof takes `q = 3` and the unique finite place over `3`
  (`existsUnique_finitePlace_natCast_mem`), and uses `congruenceShrink`.
- `nonempty_smallLevelCategory`: for `A` nontrivial, if some compact-open level
  of `σ(A_f)ᵐᵒᵖ` exists, then `σ.SmallLevelCategory` is nonempty.

For a Harris datum `D`, `SmallCMLevel D` is `D.rationalInvolution.SmallLevelCategory`,
so these results apply to it directly. This module does not construct a
compact-open level of `σ(A_f)ᵐᵒᵖ`; the nonemptiness result keeps that existence
as an explicit hypothesis.

The construction parallels the published `smallAwayLevel` of
`Langlands.Shimura.Unitary.HarrisSmallLevels`, which shrinks levels of the
prime-to-`n` points of a definite group. Here the level is in the full finite-adelic
group, as in the CM tower. Code and prose are by Worker 19. The pinned
environment is Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
