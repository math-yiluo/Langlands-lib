# Strict dominant displacement outside the actual Levi Weyl subgroup

Author: Worker 135. This module constructs the subgroup of actual relative
Weyl elements preserving restriction of every full real character along a
torus morphism. For a compatible parabolic presentation, it proves the strict
dominant displacement bound after restriction to the actual Levi split
component. This is an intermediate result for Task 5282; it does not prove
opposite regularity or identify the exponents of a twisted Jacquet module.

## Exact content

The construction `relativeWeylRestrictionStabilizer i f` is a subgroup of the
actual quotient `relativeWeylGroup i`. Its elements preserve the real
restriction map along the specified torus morphism `f : A -> T` on every
`x : Vstar T`. It is not a quotient scheme or an abstract replacement Weyl
group.

Fix a compatible presentation `r` of actual maps `P -> G`, `M -> P`, and
`A -> M`, with `k : Type u` an arbitrary field. In the parabolic section,
affineness and local finite type of `G` are explicit instances. The theorem
`standardRelativeWeylGroup_le_restrictionStabilizer` proves that the actual
standard Levi Weyl subgroup fixes this restriction, using a supplied finite
Coxeter realization and integral reflection data `D`.

For a full real character `x` pairing nonnegatively with every simple coroot
of `D` and strictly positively with every simple coroot outside `r.data.J`,
`restrict_displacement_eq_zero_iff_of_coxeter` proves

```
restriction (x - w x) = 0 iff w belongs to the actual Levi Weyl subgroup.
```

The connected reductive version `restrict_displacement_eq_zero_iff` supplies
the finite Coxeter realization using the proved `relativeWeylCoxeter`.
`evaluation_restrict_displacement_pos` says that the defining split-component
functional evaluates this displacement strictly positively when `w` is
outside that subgroup.

Finally,
`exists_lift_strict_displacement_of_mem_restrictedCorootChamber` uses exactly
the published open coroot chamber: every parameter `paramA` in that chamber
has one lift `x` to the full real torus character space such that, for every
actual `w` outside the Levi subgroup,

```
restriction (w x) = paramA - delta,
where delta belongs to r.nonnegCone and delta is nonzero.
```

The chamber's selected-coroot vanishing supplies the required nonnegative
simple-coroot values. The lift is existential, as in the chamber definition.
No unproved strict-displacement, invariant inner-product, minimal-representative
or additional positivity assumption is used. Rank zero and the whole-Levi
case are included; their outside-subgroup assertions can be vacuous.

## Implemented proof

Selected simple roots restrict to zero along `r.data.f`. Thus their full
reflection formulas imply that the corresponding actual simple generators
preserve restriction of every real character. The Coxeter realization's
parabolic-subgroup clause and subgroup closure prove the standard Levi
subgroup inclusion in the restriction stabilizer.

For the zero-displacement criterion, use strong induction on Coxeter length.
Write `w = v s_a` with shorter `v`. The preceding module gives

```
restriction (x - w x)
  = restriction (x - v x) + <x, a^vee> * restriction (v a),
```

with both terms in the actual nonnegative parabolic cone. If their sum is
zero, the strictly positive defining functional forces the first term to be
zero. Induction places `v` in the Levi subgroup, so restriction of `v a`
equals restriction of `a`. If `a` were outside the selected simple roots,
its coroot coefficient and the defining evaluation of its restricted root
would both be strictly positive, contradicting the zero sum. Thus `a` is
selected and both factors belong to the Levi subgroup. The converse follows
from the previously proved restriction stabilizer inclusion.

The connected reductive version, strict evaluation and chamber-lift theorem
compose this criterion with the preceding displacement cone bound. In
particular, the proof establishes strictness after restriction directly;
it does not infer it from nonvanishing of an unprojected vector.

## Source and remaining use

David Renard, *Representations des groupes reductifs p-adiques*, French version
of 9 July 2026, literature ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 135 read VII.4.1's Lemma and proof, printed pp.241--242 / PDF
pp.247--248. The strict projected parameter displacement is equation
(VII.4.1.2); its nonnegative precursor is (VII.4.1.3). This module gives a
derived actual-object formulation. Applying its result to `w` inverse gives
the book's inverse-action convention. The implemented proof uses the
length induction and cone functional above instead of the book's
minimal-double-coset representative argument.

For the host regularity theorem, one must still transport the actual
unramified twisting parameter through the Jacquet and conjugation functors,
compare its full geometric-lemma piece with the Weyl expression, and connect
nonidentity parabolic double cosets to quotient classes outside the Levi
Weyl subgroup. The inducing-side exponent equality is already in
`NormalizedTemperedTwistExponent`. The opposite identity-support equivalence
and the general represented geometric-lemma and regularity-criterion inputs
are separate proof obligations with their existing owners.
