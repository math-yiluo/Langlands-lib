# A compatible subgroup torus inside a prescribed geometric maximal torus

Author: Worker 1632.

This internal specialization works over an algebraically closed field `k`
in arbitrary universe `u`. The actual ambient group `G` is smooth, affine
and connected. A supplied closed map `d : D → G` represents a normal
subgroup functor. The ambient maximal torus `t : T → G` is prescribed.

`SubgroupFunctor.IsRepresentedBy.exists_compatible_maximalTorus_of_isAlgClosed`
constructs an actual split maximal torus `a : S → D` and an actual closed
torus map `φ : S → T` satisfying `groupHom φ ≫ t = a ≫ d`.
It retains both the prescribed ambient torus `T` and the prescribed
embedding `t`.

`CompatibleSubgroupTorus t d` stores this actual split torus `S`, its
maximal embedding in `D`, its closed map to the unchanged `T`, and the
commuting-square identity. The record itself only packages these data;
its definition does not use algebraic closedness or the ambient smoothness,
affineness and connectedness hypotheses.

The published finite-Galois splitting theorem implies that every torus
over the algebraically closed field is split. Hence maximal split tori
are maximal tori. The published geometric maximal-torus conjugacy theorem
therefore gives conjugacy of maximal split tori in `G`. The existing
normal-subgroup conjugacy reduction then constructs a compatible maximal
split torus of `D` inside the prescribed `T`. Its proof extends a maximal
split torus of `D` to one of `G`, conjugates that ambient torus to the
prescribed one, and uses normality to restrict the same inner automorphism
to `D`. The reduction also proves closedness of the resulting map to `T`.
The splitting property converts the returned subgroup maximal split torus
to a maximal torus, yielding the claimed conclusion.

`IsDerivedSubgroup.exists_compatible_maximalTorus_of_isAlgClosed` applies
this construction to every actual full derived subgroup. Its closedness,
representation and normality follow from `IsDerivedSubgroup`.
No reductivity or semisimplicity of `D`, actual root datum, root-span
comparison, or full-intersection torus hypothesis is needed.

`SubgroupFunctor.IsRepresentedBy.geometricSubgroupTorus` chooses the
compatible record from the proved existence by classical choice.
`IsDerivedSubgroup.geometricSubgroupTorus` supplies the corresponding
record for the actual full derived subgroup, using its closedness,
representation and normality. Both constructors retain the same
geometric assumptions as the existence theorems.

The provenance is this internal composition of published geometric
conjugacy, splitting and normal-subgroup transport constructions; no
literature theorem is transcribed. The result is a geometric
specialization of the conditional all-field derived maximal-split-torus
reduction. It does not prove the stronger arbitrary-field
`DerivedMaximalSplitTorusStatement`, descend the constructed subgroup torus
to a smaller field, or identify it with the full scheme-theoretic
intersection `T ×_G D`. In the Levi cocenter application it supplies the
compatible subgroup torus only over an algebraic closure, for a character
comparison subsequently reflected to the chosen splitting field.
