# The norm-square cover on coefficient algebras

Authors: Worker 124.

This internal construction uses the published unconditional reduced norm
`Langlands.CentralSimple.reducedNormUnits`. Let `K` be a field and `A` a
finite-dimensional central simple `K`-algebra, both in an arbitrary common
universe. For every commutative `K`-algebra `R`, `normSquareCover K A R`
is the actual subgroup of
`(R ⊗[K] A)ˣ × Rˣ` consisting of pairs `(a,t)` with `Nrd(a)=t²`.
The algebra `R` may be nonreduced or trivial.

The first projection has image exactly the units with square reduced norm.
The second projection is an actual chosen square root. The norm-one factor
maps to this group by `a ↦ (a,1)`.

Under the explicit hypothesis `reducedDegree K A = 2`, scalar units have
reduced norm equal to their square. Thus the scalar lift is
`t ↦ (t·1,t)`, and it commutes with the norm-one lift. Multiplication gives
`normSquareProductEquiv`, a multiplicative equivalence from
`reducedNormOne K A R × Rˣ` to the norm-square cover. Its inverse sends
`(a,t)` to `(a(t·1)⁻¹,t)`. The norm of the first coordinate is one by the
defining equation for the cover and the scalar norm formula. The inverse
identities use only group cancellation.

The final generation lemma says that a subgroup containing both actual
lifted factors is the full cover. It includes the kernel of the first
projection without requiring a separate choice of signs.

This pair defines a group on coefficient algebras and proves its elementary
algebraic properties. It makes no assertion that this group is a subgroup of
a supplied spin cover or that either lifted factor is elementary in a spin
group. Those geometric and generation comparisons remain separate work.
There is no characteristic restriction and no assertion that square roots
of one are exhausted by distinct signs over arbitrary `R`.
