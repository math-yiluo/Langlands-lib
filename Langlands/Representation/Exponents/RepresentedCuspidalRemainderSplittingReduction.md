# The represented cuspidal/remainder splitting from (KF)

Worker 837 authored the assembly proof. Worker 1750 added the named
Prop-valued reduction statement and prepared this supporting unit for review.
The module reuses Worker 491's norm-kernel compact
projector components, Worker 1750's comparison of represented and standard
cuspidality (through `RepresentedCompactRestrictionSupercuspidal`), and the
published standard-family compact-restriction results.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The module
implements the first part of the proof of VI.3.5 Theorem, printed pp.146–147 /
PDF pp.152–153, in the two-summand form of the published target. Renard writes
`Res V = V_c ⊕ V_nc` for the restriction to `⁰G`, obtains stability under `G`
from uniqueness, and uses VI.2.1 to place `V_c` in `M(G)_sc` and `V_nc` in
`M(G)_ind`. The finer decomposition of `M(G)_sc` into inertia classes is not
treated here.

## The theorem

`RepresentedCuspidalRemainderSplittingReductionStatement.{u, v}` is the
implication from the six propositions listed below to the exact published
`RepresentedCuspidalRemainderSplittingStatement.{u, v}`. The theorem
`representedCuspidalRemainderSplitting_of_fixedLevelFiniteness` proves this
implication with its six inputs named explicitly, in independent field
universe `u` and carrier universe `v`. It assumes these propositions:

- `hKF : CuspidalSupport.RationalNormKernelFixedLevelFinitenessStatement.{u, v}`,
  the condition (KF) of IV.1.7, which Renard verifies in the proof of VI.3.4
  (printed pp.145–146 / PDF pp.151–152). For an actual maximal split torus,
  a generic cocharacter and the listed structural inputs, it states that every
  compact open subgroup of the norm kernel `Plancherel.rationalCommonNormKernel G`
  fixes nonzero vectors in only finitely many compact irreducible smooth
  isomorphism classes;
- `hPD : ParabolicDynamicStatement`;
- `hconj : SmoothMaximalSplitTorusConjugacyStatement`;
- `hStandard : StandardCocharacterStatement`;
- `hRoot : RelativeRootSystemStatement`;
- `hJoint : JointSpecialCompactBasisExistenceStatement`.

None of these six propositions is proved in this module. The conclusion
quantifies over every nonarchimedean local field, every connected reductive
group, and every smooth complex representation `A` of its rational points with
the canonical point topology. It adds no torus, cocharacter, admissibility,
finite-length or irreducibility hypothesis.

## Implemented proof

The proof introduces the data of the target statement. It then derives that
`G.X.left` is affine, that `G` is smooth, and that the rational-point group is
Hausdorff (published `rationalPoint_t2Space`). It chooses one standard family
internally. The published `exists_maximalSplitTorus_genericCocharacter hG`
gives an actual maximal split torus `i` and a generic cocharacter `ν`, `hRoot`
gives the relative root system of `i`, and the published
`isClosed_unipotent_of_isNonarchimedeanLocalField` closes the standard
unipotent subgroups. Applying `hKF` to this family and to `hStandard` gives
`hstrata`, the finiteness of the compact-class fixed stratum for every compact
open subgroup of the norm kernel. Its topology `rationalPointTopology k G.X`
is the target's `RationalPointFamily.pointTopology`.

The components are Worker 491's
`CuspidalSupport.rationalNormKernelCompactComponents G hstrata A`. At `true`
this is the range of the ambient norm-kernel compact projector
`rationalNormKernelCompactProjector G hstrata A`, and at `false` its kernel.
The maps are the inclusions of `rationalNormKernelCompactCofan`, and
`rationalNormKernelCompactCofanIsColimit` is the coproduct property required
by `HasCuspidalRemainderSplitting`. The projector is an intertwiner of the
ambient representation, so both components are subrepresentations of `A`.
This plays the role of Renard's stability argument.
`rationalNormKernelCompactComponents_mem` places the range in the factor whose
every actual subquotient has compact norm-kernel restriction, and the kernel
in the factor with no nontrivial such subquotient. The Library's
`SmoothRep.compactRestrictionProperty (Plancherel.rationalCommonNormKernel G)`
is definitionally `HasCompactNormKernelRestriction`.

- Cuspidal component. Membership at `true`, applied to the component itself
  (`SmoothRep.isSubquotient_self`, imported from `SharpCuspidalSeriesReduction`),
  gives its compact norm-kernel restriction.
  `isSupercuspidal_of_compactRestriction` (VI.2.1, (c) implies (a), using
  `hPD`, `hconj`, `hStandard` and `hRoot`) then shows that it is supercuspidal
  for every proper actual parabolic.
- Remainder. Let `D` be a nontrivial actual subquotient of the kernel and
  suppose `D` is supercuspidal. `compactRestriction_of_isSupercuspidal`
  (VI.2.1, (a) implies (c), using `hPD`, `hStandard`, `hRoot` and `hJoint`)
  gives compact norm-kernel restriction of `D`, which membership at `false`
  excludes. So the remainder has no nonzero supercuspidal subquotient.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Scope

The module proves no structural existence statement and does not prove (KF).
The unconditional target follows by applying this theorem once (KF) and the
five structural statements are proved. This is a supporting conditional
statement and assembly proof; its submission does not claim completion of
the host task or acceptance of an unconditional splitting proof.
