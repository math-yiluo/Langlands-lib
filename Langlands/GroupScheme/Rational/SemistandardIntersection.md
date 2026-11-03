# Actual Levi and radical interfaces for semistandard intersections

This module supplies conclusion predicates for the separate general
semistandard-intersection target. It asserts no structural existence theorem.
The base is an arbitrary field in universe `u`, and subgroup functors are
evaluated on all schemes over that field, including nonreduced schemes.

`IsGeometricUnipotentRadical r`, for `r : R → H`, says that `r` is a
closed subgroup, `R` is smooth, connected and unipotent, and its range is
normal on every test. Over the chosen algebraic closure, `R` remains
connected and unipotent, its base-changed range is normal, and every
smooth connected normal unipotent closed subgroup of the base-changed
`H` has range contained in that base-changed range. Thus the predicate
specifies the geometric unipotent radical by its maximality; it does not
merely give a normal subgroup called a radical. Smoothness of the base
change follows from smoothness over the ground field. No existence or
descent of such a radical is asserted here.

`SubgroupFunctor.IsParabolicWithLeviAndRadical P L U` requires actual
group schemes `H`, `K`, `R` and maps `j : H → G`, `l : K → H`,
`r : R → H`. The map `j` represents `P` on every test and satisfies
the existing `IsParabolicSubgroup`. The map `l` is closed, `K` is
connected reductive in the existing geometric sense, and the range of
`l ≫ j` is exactly `L`. The map `r` satisfies
`IsGeometricUnipotentRadical`, and the range of `r ≫ j` is exactly
`U`. On every test, `U(X)` and `L(X)` lie in `P(X)`, `U(X)` is
normal there, and the two subgroups are complementary. The latter clause
is the bijectivity of multiplication `U(X) × L(X) → P(X)`. The
additional displayed equality is the ordered product `P(X) = L(X)U(X)`.
All these clauses are conclusions to be established, rather than
assumptions of the later reductive-group statement.

`IsParabolicWithLeviAndRadical.isParabolicFunctor` only forgets the
additional structure and supplies the existing `IsParabolicFunctor P`.
Its proof takes the representative `H,j` and the range equality from
`P.IsRepresentedBy j`.

`SemistandardIntersectionProducts M N Q L U` is the pair of equalities

- `M ∩ Q = (M ∩ L)(M ∩ U)`;
- `N ∩ Q = (N ∩ L)(N ∩ U)`.

Each is a literal equality of subsets of `Hom(X,G)` for every test
scheme `X`, using pointwise multiplication. It is not an equality of
generated subgroups. Its `identityTest` theorem evaluates the supplied
predicate at `Spec k → Spec k`, giving exactly the actual rational-point
formulas. That theorem is a direct specialization, not a proof of the
general intersection assertion.

## Sources and derived packaging

Renard, 9 July 2026 edition, V.3.8 and V.3.10, printed pp.111–112
(PDF pp.117–118), fixes one maximal split torus and chooses the Levi
containing it. For two semistandard parabolics `P=MN`, `Q=LU`,
V.3.10 identifies the parabolic `M ∩ Q`, its Levi `M ∩ L`, its
unipotent radical `M ∩ U`, and the second product above. The first
product and unique normal decomposition express the asserted Levi
decomposition. No nesting of `P,Q` is part of that passage.

The radical predicate uses the definition of unipotence and the largest
smooth connected normal unipotent subgroup in Milne 2017, §6.45–6.46,
printed p.135 (PDF p.151), together with the Library's existing
`IsUnipotent` and base-change conventions. The geometric maximality
clause records the radical after extension to an algebraic closure,
instead of identifying the ground-field unipotent radical with the
geometric one without a condition.

The arbitrary-field, represented-subgroup and all-test formulation is
derived. Borel–Tits 1965 §0.3, printed pp.57–58 (PDF pp.4–5),
permits the affine absolutely reduced scheme interpretation. Sections
4.4(c) and 4.7, printed pp.86–88 (PDF pp.33–35), describe the
parabolic-in-Levi structure and rationality of intersections and Levi
factors. Milne §25.1, §25.6–25.7, printed pp.544–546
(PDF pp.560–562), gives the cocharacter and parabolic-intersection
framework. These motivate the later dynamic target; they are not a
Lean proof of the predicates or a literal all-test formulation in Renard.

The official Milne errata has been checked. The corrected §25.6(b)
concerns minimal parabolics, and its relative-root-system proof warning
does not supply a root-classification axiom here. The new definitions
do not assert that an arbitrary Levi is the centralizer of a maximal
split torus. The 2010 Renard correction requiring semistandard `P,Q`
in VI.1.4 concerns the separate nested target; V.3.10 already states
its common semistandard setting explicitly.

Source IDs: `renard-2026-representations-groupes-reductifs-padiques`,
`borel-tits-1965-groupes-reductifs`,
`milne-2017-algebraic-groups`, and
`milne-2017-algebraic-groups-errata-2026-11-02`.
