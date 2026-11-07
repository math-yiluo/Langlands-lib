# Represented supercuspidality and compact norm-kernel restriction

This internal supporting module for the represented cuspidal/remainder
splitting proves Renard VI.2.1 Theorem, (a) iff (c), where supercuspidality is
tested on every proper actual rational parabolic. The source is David Renard,
*Représentations des groupes réductifs p-adiques*, French version of
9 July 2026, VI.2.1, printed pp.137–138 / PDF pp.143–144. It is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The module states condition (b), compactness modulo the centre, nowhere.

## The definition

`HasCompactNormKernelRestriction A` is Renard's condition (c): "la
restriction de (π,V) à ⁰G est compacte". The group `⁰G` is the published
`Plancherel.rationalCommonNormKernel G`, the intersection of the kernels of
the normalized absolute values of all actual rational characters (Renard
V.2.3). The rational points carry the canonical `pointTopology`, and `⁰G`
carries the subgroup topology. "Compact" is the Library's
`HasCompactSmoothDualCoefficients` for the restricted action
`SmoothRep.restrictSubgroup (rationalCommonNormKernel G) A`. That predicate
requires every coefficient against a vector of `A` and a smooth vector of the
algebraic dual of the restricted action to have compact support in `⁰G`.
The definition names the antecedent of the published
`RationalCompactRestrictionCuspidalStatement`, which is also the conclusion of
`RationalCuspidalCompactRestrictionStatement`. It imposes no
irreducibility, admissibility or finite-length condition.

## The theorems

All three theorems work over an arbitrary nonarchimedean local field `k` and
an actual connected reductive group scheme `G` (`hG`). The rational points
carry the canonical topology, which is assumed locally compact and
nonarchimedean, and the field is Hausdorff. The representation `A` is an
arbitrary smooth complex representation. The field and carrier universes
`u` and `v` are independent. The represented `IsSupercuspidal A` is the
published predicate: Jacquet vanishing for every proper actual parabolic
`p`, every rational Levi `l` and every geometric unipotent radical `r` with
bijective multiplication. Renard VI.2.1 Definition quantifies over all
proper parabolics in the same way.

The following universal structural statements are explicit hypotheses and
are not proved in this module:

- `hPD : ParabolicDynamicStatement` (parabolics are dynamic);
- `hconj : SmoothMaximalSplitTorusConjugacyStatement` (only in the reverse
  direction);
- `hStandard : StandardCocharacterStatement`;
- `hRoot : RelativeRootSystemStatement`;
- `hJoint : JointSpecialCompactBasisExistenceStatement` (only in the forward
  direction).

`isSupercuspidal_of_compactRestriction` proves (c) implies (a).
`compactRestriction_of_isSupercuspidal` proves (a) implies (c).
`isSupercuspidal_iff_compactRestriction` combines the two.

## Implemented proof

Both directions choose one standard family internally. The published
`exists_maximalSplitTorus_genericCocharacter hG` gives an actual maximal split
torus `i : T.toGrp ⟶ G` and a generic cocharacter `ν`. `hRoot` gives the
actual relative root system of `i`, and `simpleRelativeRootFintype` makes its
simple roots finite. The published
`isClosed_unipotent_of_isNonarchimedeanLocalField` proves that every actual
standard unipotent subgroup is closed. The rational-point group is Hausdorff
by the published `rationalPoint_t2Space`. The choice is internal, so neither
statement depends on a torus or cocharacter.

(c) implies (a). The published `rationalCompactRestrictionCuspidal` (Renard
VI.2.1, (c) implies (a), for proper standard parabolics) turns the compact
restriction into `IsCuspidal` for the chosen standard family. Worker 1750's
`isSupercuspidal_of_isCuspidal` in `RepresentedCuspidalityComparison`
conjugates every proper actual parabolic to a standard one, using `hPD` and
`hconj`, and transfers the vanishing of the coinvariants. This is the
reduction "sans perte de généralité, on peut supposer que P est standard" in
Renard's proof, and Remark 1 of VI.2.1.

(a) implies (c). Renard's proof passes through (b); the implemented route
does not. The published `isCuspidal_of_all_represented_parabolics`
specializes `IsSupercuspidal A` to the proper standard parabolics of the
chosen family and gives `IsCuspidal`. Here `hPD` and `hStandard` show that
each proper standard representative is an actual parabolic with a rational
Levi and a geometric unipotent radical. `hJoint` supplies one apartment datum `D`, one point `x`, an
actual torus centralizer `j : Z ⟶ G` with `s ≫ j = i`, and its character
comparison. It also gives the special-compact vertex and property clauses,
the ambient Cartan comparison and the simultaneous Renard basis. The
published `rationalPositiveCartanCover` turns that Cartan comparison into a
finite positive Cartan cover of the same special compact subgroup. The
published `rationalCuspidalCompactRestriction` then gives the compact
norm-kernel restriction. It bounds the support of the coefficients inside
`⁰G` directly.

The iff pairs the two implications. The axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## Scope

The module proves no structural existence statement. It does not prove the
fixed-level finiteness on the norm kernel, and it does not construct a
cuspidal/remainder splitting. The final splitting proof will apply these
theorems once the structural statements are proved.
