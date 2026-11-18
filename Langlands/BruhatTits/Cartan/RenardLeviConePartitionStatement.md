# Renard V.3.21.1 modulo the common norm kernel

Author: Worker 1222.

`Langlands.BruhatTits.Cartan.RenardLeviCones.LeviConePartitionStatement`
states a partition of the image of `A_M^+` in `A_M(F)/⁰A_M` for every
standard parabolic `P = MN`. Each piece comes from `A_L^{++}` for a standard
parabolic `Q = LU` containing `P`.

The field `F : Type u` is nonarchimedean local. The connected reductive
`F`-group scheme `G` has maximal split torus `i : T → G` and generic
cocharacter `ν`. Write `R = simpleRelativeRoots i ν`. The index
`J ⊆ R` identifies `P` and its canonical standard Levi representative
`M = Standard.leviScheme i ν J`. The inputs include an arbitrary actual
split component `a : A → M` and a map `f : A → T` whose composite with `i`
agrees with `a` followed by the inclusion of `M` into `G`.

The projection `q` takes rational points of `A` to their classes modulo
`rationalCommonNormKernel A.toGrp`. This kernel is the maximal compact
subgroup `⁰A_M` of the split torus, by
`SplitTorus.isCompact_commonNormKernel` and
`compactSubgroup_le_rationalCommonNormKernel`. The cone is the image under `q`
of the full rational-point set `componentPlus F i ν J f`.

The piece at `K` consists of classes represented by some point of
`componentStrict F i ν K (g ≫ f)` mapped through `g : B → A`.
Here `J ⊆ K ⊆ R`, `b : B → Standard.leviScheme i ν K` is a split
component, and the composite `B → A → T → G` equals the composite of `b`
with the standard Levi inclusion into `G`. The proposition quantifies over
these witnesses in membership. The conclusion gives containment of each
piece in the cone and exactly one index `K` for each class in the cone.
`standardParabolicOrder` identifies the interval of indices with the
standard parabolics containing `P`.

This is a correction derived from David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`. V.3.21
(printed p. 116 / PDF p. 122) gives the norm conditions and asserts a
partition of `A_M^+` on points in (V.3.21.1), invoking the chamber
decompositions of V.3.16 (printed pp. 113–114 / PDF pp. 119–120).
V.3.13 (printed pp. 112–113 / PDF pp. 118–119) gives the inclusion
`A_L ⊆ A_M`. V.2.5 (printed p. 107 / PDF p. 113) identifies `⁰A` for a
split torus. Issue I1 in the Chapter V item ledger records the obstruction
to the printed pointwise formula. For the standard Borel of `GL₂`, a
nonidentity unit `u` makes `diag(1,u)` a point of the nonnegative cone
with root norm one, while the element is outside both the strict Borel
cone and the split centre. Its quotient class is represented by the
identity.

The quotient keeps precisely the rational-character valuations. The
zero simple-root coordinates of a class determine the standard Levi
index, and the positive coordinates give the strict inequalities for its
piece. The statement applies to every standard index `J`, including the
unique index in relative rank zero. It uses the full cones defined in
[RenardLeviCones](RenardLeviCones.md).
