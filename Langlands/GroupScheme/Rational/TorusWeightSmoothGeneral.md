# Smoothness for arbitrary semigroups of torus weights

Let `F` be a group-valued functor on commutative algebras over a commutative
ring `R` in universe `u`, corepresented by a commutative `R`-algebra `B` via
`e`, and let `σ : TorusAction F I` be an action of a split torus indexed by a
finite type `I`. Assume `B` is formally smooth over `R`. This module proves
that `B ⧸ weightIdeal e σ P` is formally smooth for every additive
subsemigroup `P` of `I → ℤ`. There is no restriction on whether `P` contains
zero; the empty semigroup is also allowed. If `R` is Noetherian and `B` is
of finite type over `R`, the quotient algebra is smooth over `R`.

`exists_lift_mem_weightSubgroup_of_zero_mem` supplies square-zero lifts of
points of the existing coordinate weight subgroup when `0 ∈ P`.
`exists_lift_mem_weightSubgroup_all` combines that result with the published
zero-excluding case. `weightSubgroupLift` chooses an actual point of the
weight subgroup lifting the prescribed quotient point, and
`map_weightSubgroupLift` proves its reduction equation. This choice is
noncanonical; no naturality or compatibility with multiplication is
asserted. `formallySmooth_quotient_weightIdeal_all` translates
point lifting into formal smoothness of the quotient algebra.
`smooth_quotient_weightIdeal` adds finite presentation over a Noetherian
base. All declarations lie in `Langlands.GroupScheme.Corepresented`.

The new zero-containing case adapts the first three steps of Worker 1224's
published `Rational.TorusWeightSmooth` lifting proof. Twist the given point by the
universal torus units, so its coordinates have support in `{0} ∪ P`. Lift
this point through the surjective, square-zero reduction map between
supported subalgebras, using formal smoothness of `B`. Untwist the lifted
point. Its nonconstant Laurent coefficients lie in the square-zero ideal,
so taking the constant coefficient defines an algebra homomorphism. The
resulting point `v` reduces to the given point and its coordinates vanish
on weight components outside `{0} ∪ P`. When `0 ∈ P`, this is the same as
being outside `P`; those weights are nonzero, and their augmentations
vanish. Thus `v` already belongs to the requested weight subgroup.

For the quotient algebra, compose a proposed quotient-algebra point with
the quotient map to get a point of the weight subgroup, lift the point,
and factor its coordinates back through the weight ideal. Over a
Noetherian base, a finite-type quotient algebra is finitely presented;
together with the established formal smoothness this gives smoothness.

This is an internal derivation using the published coordinate action,
weight ideal, supported-algebra lifting lemmas, and Mathlib's formal
smoothness criterion. It extends the zero-excluding result without changing
its interface. It does not identify the coordinate weight subgroup with the
all-test generated semigroup subgroup, construct its connected component,
or prove the full semigroup realization or split-unipotence statement.
