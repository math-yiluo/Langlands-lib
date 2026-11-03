# Finite length of actual supercuspidal induction: statement

`Langlands.Aubert.General.RationalPointFamily.RationalSupercuspidalInductionFiniteLengthStatement`
is a Prop-valued statement interface for the finite-length assertion in Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, Théorème VI.5.4, printed pp.173–174 / PDF pp.179–180. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This module defines the proposition and supplies no proof of it.

VI.5.4 asserts that normalized induction of an irreducible supercuspidal
representation of a parabolic's Levi has finite length, bounded by `l(M)`.
Only finite length is represented here. The explicit bound, the equivalences
involving association, nonzero Hom, common irreducible constituents and
Jordan–Hölder series, and the additional bound on the Hom dimension are outside
this declaration. Its proof is a later obligation; Renard's proof on printed
p.174 uses supercuspidal Jacquet detection, VI.5.3 and exactness. This module
does not assume those representation-theoretic results.

## Actual groups, topology and universes

The quantifiers range over every nonarchimedean local field `k : Type u` and
every connected reductive group scheme `G` over `Spec k`, with a maximal split
torus `i : T.toGrp ⟶ G` and a generic cocharacter `ν`. The ambient group is
literally `RationalPoint k G.X`, the identity-test rational-point group. For a
finite subset `I` of the actual simple-root labels `SimpleRoot i ν`, the
subgroups are exactly the published `parabolic i ν I`, `levi i ν I` and
`unipotent i ν I`. These evaluate the corresponding standard subgroup functors
at `Over.mk (𝟙 _)`, at the root subset `rootSet i ν I`. No abstract replacement
group or freely supplied decomposition is used.

The installed topology is `RationalPointFamily.pointTopology`: the affine
evaluation topology on base-valued ring points, transported to the identity-test
carrier by the published rational-point equivalence. Affineness follows from
`hG`. Each subgroup has its induced topology. Ambient local compactness,
`NonarchimedeanGroup` and Hausdorffness are explicit structural instances on
this precise topology; `NonarchimedeanGroup` includes the topological-group
laws.

Coefficients are `ℂ`. The input is exactly
`σ : SmoothRep.{0, u, uV} ℂ (levi i ν I)`, with carrier in `Type uV`, where
`uV` is independent of `u`. The existing normalized induction functor has
output `SmoothRep.{0, u, max u uV} ℂ (RationalPoint k G.X)`. The input carrier
is not replaced by that larger universe. There is no characteristic-zero,
split-group, admissibility or finite-dimensionality restriction.

Every standard index occurs, including `I = Finset.univ`; there is no
properness restriction on the inducing parabolic. Thus the index for induction
from the full Levi is retained. The actual endpoint identifications are
structural comparison obligations: for example, the published
`standardParabolic_univ` and `standardUnipotent_univ` use
`StandardParabolicEndpointsStatement`. This new proposition neither assumes nor
proves that endpoint statement.

## Premises and conclusion

The local `h I` is constructed by
`isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I`.
It is the published decomposition of these actual ambient point subgroups.
The local `hL I K` is constructed by
`isSemidirectDecomposition_in_levi i ν hInter hG hi hν I K`.
For `K : Finset I` and `J = leviIndex I K`, it decomposes the actual inner
parabolic `(parabolic i ν J).subgroupOf (levi i ν I)`, with Levi
`(levi i ν J).subgroupOf (levi i ν I)` and radical
`(unipotent i ν J).subgroupOf (levi i ν I)`.

The two representation-theoretic premises are precisely `σ.IsIrreducible` and
the existing `IsLeviCuspidal` predicate for this family and `hL I`.
Irreducibility is the existing nonzero irreducibility predicate.
`IsLeviCuspidal` says that for every `K : Finset I` with
`K ≠ Finset.univ`, the carrier of the normalized Jacquet module inside this
same Levi is `Subsingleton`, hence zero. Since `I` is finite, these are exactly
its proper subsets. The predicate does not itself assume irreducibility.
`hM I` supplies local compactness of the Levi; closedness of each inner radical
is obtained by pulling back `hU J` under the continuous subtype map.

Renard VI.2.1, printed p.137 / PDF p.143, defines supercuspidality by vanishing
normalized Jacquet modules along every proper parabolic, and its first remark
states that proper standard parabolics suffice. The comparison of that
all-proper-parabolic convention with this actual inner standard family still
requires the structural identification and conjugation/Jacquet comparison in
the actual Levi. This module records the proper-standard predicate and does
not prove that comparison or insert it as an extra premise.

The conclusion is exactly
`((normalizedInductionFunctor.{u, uV} (h I) (hU I)).obj σ).HasFiniteLength`.
Here `SmoothRep.HasFiniteLength` is the existing group-algebra predicate
`IsFiniteLength ℂ[H] A.representation.asModule` for
`H = RationalPoint k G.X`. It asserts finite composition length of the actual
induced representation, not finite complex dimension.

## Normalization comparison

The functor is the existing full-parabolic Haar-normalized functor from
`General.Parabolic`. It inflates `σ` along the actual projection
`(h I).projection : parabolic i ν I →* levi i ν I`, twists on the whole
parabolic by
`χ_P = HaarModulus.closedHalfCharacter (unipotent i ν I) (hU I)
  (parabolic i ν I) (h I).le_normalizer`,
and takes smooth induction with right translation. Its function covariance is
`f(p g) = χ_P(p) • σ((h I).projection p)(f(g))`, with the character coerced
from complex units.

Renard VI.1.2, printed pp.135–136 / PDF pp.141–142, uses the Levi twist
`δ_P^(-1/2)` inflated to the parabolic. His remark on p.136 identifies his
modular convention as inverse to the usual one; see also V.5.4, printed
pp.126–127 / PDF pp.132–133. No equality with the Library character is claimed
here. The existing `closedHalfCharacter_levi` gives the restriction to the
Levi. The stronger `closedHalfCharacter_eq_comp_projection` identifies the
full-parabolic character with inflation of that restriction only under
`IsUnimodularModulus` of the radical. The published compact-subgroup-limit
criterion can establish that hypothesis, but it must still be applied to
these actual radicals, and the source modulus/sign must be compared. These
normalization comparisons remain proof obligations; unimodularity and a
character equality are not additional premises of this statement.

## Retained structural obligations and scope

The intermediate interface explicitly retains the following structural inputs.
They must eventually be established for the actual families to recover the
unconditional source assertion.

- `hStandard : StandardCocharacterStatement.{u}` is the named global
  standard-cocharacter existence and dynamic-comparison assertion. Its
  specialization supplies `h`, rather than assuming a decomposition family.
  The named structural assertion remains to be discharged.
- `hInter : StandardLeviIntersectionStatement.{u}` is the named global
  all-test inner-Levi decomposition and rational unipotent-product assertion.
  The adapter uses its first conjunct at the identity test, then restricts to
  the actual Levi. The premise retains the entire named statement, whose
  discharge is a structural obligation.
- `hRoots : HasRelativeRootSystem i` supplies `simpleRelativeRootFintype`
  together with the split-subtorus property derived from `hi`. It must be
  established for the given maximal split torus.
- `hU` and `hM` assert closedness of all actual standard radicals and Levis
  in the canonical topology. These closedness assertions remain to be proved.
- The three ambient topological instances described above must be established
  for the canonical point topology over the local field.

The source-to-standard cuspidality and normalization comparisons described
above are also retained obligations. No finite-length conclusion, cuspidal
embedding, geometric lemma, transitivity, admissibility, detection or support
theorem is moved into the premises.

The module leaves `DynamicInductionIrreducibleFiniteLengthStatement` and
`DynamicInductionFiniteLengthStatement` unchanged. Their proofs remain with
tasks `02257068-4b1f-4c7d-b849-c85a24606658` and
`174d2de0-fa21-41b4-b091-f1b86481790b`. The present proposition is an upstream
statement prerequisite and establishes neither target.
