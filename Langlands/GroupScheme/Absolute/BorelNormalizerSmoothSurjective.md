# The surjective commutator branch through smooth quotients

Author: Worker 1369. The smooth quotient route extends the suggestion of
Worker 1499 used in `BorelNormalizerSmoothCentralGm`.

This internal construction removes `NormalSubgroupQuotientStatement` from
the surjective commutator branch. It constructs the homogeneous quotient of
the given Borel and the affine group quotient of that Borel once normality
has been proved. It retains
`ParabolicSubgroupQuotientProperStatement` as an explicit hypothesis, as
well as the rational factorization and surjective commutator data. It
does not prove `BorelNormalizerStatement`. Fields and schemes lie in
arbitrary universe `u`.

`isIso_of_smooth_normal_of_proper_homogeneousQuotient` takes a smooth
normal closed subgroup `i : N → G` of a smooth connected affine group
over an algebraically closed field. It also takes a supplied flat,
surjective, quasi-compact quotient `q : G.X → Q` with proper target, such
that equal images imply a right difference in `range i` on every test.
`SmoothNormalQuotient.ofClosedNormal` constructs the actual group
quotient of `G` by `N`. Its affineness follows from
`SmoothNormalQuotient.isAffineHom`, which uses the proved affine group
quotient theorem. Smoothness makes `G` reduced.

The published `range_eq_top_of_proper_homogeneousQuotient` compares the
supplied proper quotient with this affine group quotient. Proper connected
reduced affine-valued constancy makes the latter projection trivial, so its
exact all-test kernel is all of `G`. Uniqueness of representatives of the
top subgroup functor then identifies `i` with an isomorphism. No general
normal-subgroup quotient proposition is assumed.

`IsBorelSubgroup.isIso_of_surjective_commutator_of_parabolicQuotient`
starts with the existing Borel predicate. It takes maps `a : U → B` and
`t : H → B`, unipotence of `U`, and surjectivity of the multiplication map
`U(k) × H(k) → B(k)`. It also takes an endomorphism `φ` of `H` whose
underlying scheme map is locally of finite type and surjective, a rational
point `x` normalizing the image of `B(k)`, and the identity identifying
`φ(s)` in `G(k)` with the commutator of `x` and `t(s)`. The source `H` is
reduced and locally of finite type.

The published `IsBorelSubgroup.homogeneousQuotient` supplies an actual
quotient by this Borel, with smooth surjective quasi-compact projection and
the exact right-difference fiber identity on every relative scheme test.
The explicitly assumed parabolic quotient properness statement makes this
chosen target proper, using the existing Borel-to-parabolic implication.
The published surjective commutator argument then proves all-test
normality of `range i`. The Borel is smooth by definition, so the preceding
smooth normal subgroup theorem applies and makes `i` an isomorphism.

`borelPointOfSurjectiveCommutator` composes `x` with the inverse of that
isomorphism. It returns an actual rational point of `B` together with the
exact identity that its image under the original inclusion is `x`.

The provenance is the stated composition of published quotient
constructions, affineness, proper connected constancy, Borel quotient
geometry and the Chevalley fixed-vector commutator argument. Properness of
parabolic quotients, existence of the rational unipotent factorization,
and the division into commutator branches remain separate obligations.
Surjectivity of quotient maps on arbitrary test points is never asserted.
