# The partition of the nonnegative quotient by actual standard-Levi pieces

Author: Worker 1222.

`Langlands.GroupScheme.CocharacterUniformizer.StandardLeviStrictQuotientPartitionStatement`
is a proposition about every nonarchimedean local field `F : Type u`,
connected reductive actual group scheme `G`, actual maximal split torus
`i : T → G`, generic cocharacter `ν`, actual split component `a₀ : A₀ → G`,
and every compatible morphism `f₀ : A₀ → T` with `f₀ ≫ i = a₀`.
Affineness of `G` is supplied by reductivity.

The target quotient is the published
`CAplusQuotient F T (simpleRelativeRoots i ν) A₀ f₀`, the image of the
nonnegative common-uniformizer section of `T` in
`T(F)/f₀(C_{A₀})`. Each strict piece is the existing
`standardLeviStrictQuotientFace F i ν A₀ f₀ J`. It uses all actual closed
representatives of the standard Levi indexed by `J`, their actual split
components, and compatible morphisms into `T`; membership requires an actual
strict common-uniformizer point.

The two clauses assert that every strict piece is contained in the nonnegative
quotient, and that every point of that quotient belongs to exactly one indexed
strict piece. Together they express both covering and disjointness, including
empty pieces. Invalid indices give empty pieces by the construction's
intrinsic law. Existence of representative data is not assumed in this target.
Neither an image equality nor a decomposition is among its premises.
The given ambient component and compatible map are retained as parameters;
their existence is a separate shared structural result.

This is the actual-object version of the strict decomposition in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, V.3.24, printed p.117 / PDF p.123, using the common-uniformizer
construction of V.2.5, printed p.107 / PDF p.113, and the lattice reading of
(V.3.21.1), printed p.116 / PDF p.122. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The use of all actual representatives and the two-clause formulation are
internal. The strict character and common-uniformizer conventions agree with
the source.

The scope includes both field characteristics, non-split ambient groups,
nonreduced relative root systems and rank zero. This is a statement target,
with no proof supplied here. It asserts no freeness or finite generation,
and no decomposition of the full rational-point cones in (V.3.21.1).
The latter full-cone assertion and the general free-monoid assertion of V.3.24
have the explicit counterexamples recorded in the Chapter V ledger.
