# Smooth dual restriction to the actual rational-character norm kernel

Author: Worker 6.

This internal adapter applies the canonical open-subgroup comparison to the
actual common rational-character norm kernel. It addresses a convention needed
in Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, VI.2.1, printed pp.137–139 / PDF pp.143–145: compactness of
the restricted smooth representation concerns its entire smooth dual. In
particular, the implication (b) to (c) on printed p.138 writes a restricted
coefficient using an ambient smooth functional. The adapter justifies that
these are the same smooth functionals for the actual open norm kernel.
The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This comparison is an internal deduction; it is not presented as a separately
numbered source assertion.

The base `F` is any field with the existing nonarchimedean-local-field
structures, including equal and mixed characteristic. The group scheme
`G` is affine and locally of finite type over `F`. These assumptions are weaker
than connected reductivity; no splitness or positive-rank restriction enters.
The point group is exactly `GroupScheme.rationalPoints G`, with the canonical
`rationalPointTopology F G.X` and its proved topological-group structure.
The subgroup is the existing `rationalCommonNormKernel G`, with its inherited
subgroup topology. It is not an arbitrary chosen subgroup.

`R` is any commutative coefficient ring and `V` any `R`-module, with coefficient,
field and carrier universes independent. The input is any algebraic
representation of the actual point group. Neither smoothness nor continuity of
this input action is required. In the book's application take `R = ℂ` and the
underlying action of an actual smooth representation. No topology is put on `V`.

The already published
`Langlands.Plancherel.rationalCommonNormOpenSubgroup G` bundles this exact
subgroup as open for the canonical topology, using the published theorem
`isOpen_rationalCommonNormKernel`. No new openness, local compactness or
closedness hypothesis is introduced here.

`isSmoothVector_dual_rationalNormKernel_iff` identifies smoothness for the full
algebraic dual of the restricted action with smoothness for the ambient dual
action. It directly reuses Worker 200's published
`Langlands.isSmoothVector_restrict_open_iff`, applied to `ρ.dual`.

`rationalNormKernelSmoothDualEquiv G ρ` is the actual representation equivalence
from the restriction of `smoothContragredient ρ` to the smooth contragredient
of the restricted action. It specializes
`Langlands.smoothContragredientRestrictOpenEquiv` from the paired generic helper
module. Its map and inverse retain the underlying algebraic functional.
The evaluation lemmas record that both maps preserve its value on every `v`.
Together with the smoothness equivalence this includes every smooth functional
on the restricted representation.

The intrinsic comparison and evaluation laws follow from these definitions
and published open-subgroup smoothness. This unit proves no compact support,
admissibility, finite-dimensionality, semisimplicity, finite restriction,
compactness of the center intersection, or implication of VI.2.1. All
Chapter V structural discharges and the remaining representation-theoretic
arguments retain their separate obligations.
