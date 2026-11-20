# Division-case quasi-projective representability through normal sublevels

Worker 3269. This module splits the published premise
`DivisionCMQuasiProjectiveRepresentabilityStatement` (module
`HarrisTaylorCMDivisionPremiseStatements`) into two closed statements. The
first is a descent statement along normal sublevels and has no division
hypothesis. The second asks for division-case representability at some
normal sublevel of each small level. The module proves that the two together
imply the premise. Given the first, it also proves that the second is
equivalent to the premise. The module then combines this with the published
premise reduction to obtain `DivisionCMRepresentabilityStatement`. It does not
prove either new statement, the premise, or the target.

All declarations live in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. They carry the same variables
and named prerequisite hypotheses as `DivisionCMRepresentabilityStatement`:
the number fields `E`, `F`, `L`, the algebra `A`, the central simple unitary
data `D`, the signature charts `C`, the named prerequisite statements
`preservation` through `polarizationStability`, the Weil transition
compatibility `compatibility`, the adelic comparison `h` and the torsion
statement `htor`. Below, "…" stands for that argument list.

`SmallCMLevel D` is the Library category of sufficiently small levels. For a
small level `U`, `U.obj.subgroup` is its compact open subgroup of the
(opposite) finite adelic group. "`U'` normal in `U`" means that
`U'.obj.subgroup ≤ U.obj.subgroup` and that
`U'.obj.subgroup.subgroupOf U.obj.subgroup` is a normal subgroup of
`U.obj.subgroup`. Normality in the whole finite adelic group is not required.
This is the convention of the Library's residual groups
`SmallCMResidualGroup D U U'`.

`CMLevelQuasiProjectiveRepresentation … U` is the published notion from
`HarrisTaylorCMDivisionCriteria`. Such data consist of a scheme over
`Spec F`, an immersion of it into a finite projective space `ℙ^dim_F` over
`Spec F`, and a natural isomorphism from its functor of points, restricted to
the componentwise admissible test category, to the existing normalized class
presheaf at `U`.

## Statements

- `CMQuasiProjectiveNormalQuotientStatement …`. For all small levels `U'`
  and `U` with `U'.obj.subgroup ≤ U.obj.subgroup` and
  `U'.obj.subgroup.subgroupOf U.obj.subgroup` normal, if quasi-projective
  representation data exist at `U'`, then they exist at `U`. No division
  hypothesis is assumed.
- `DivisionCMNormalSublevelRepresentabilityStatement …`. If `D.IsDivision`,
  then for every small level `U` there is a small level `U'` with
  `U'.obj.subgroup ≤ U.obj.subgroup`,
  `U'.obj.subgroup.subgroupOf U.obj.subgroup` normal, and quasi-projective
  representation data at `U'`.

Each statement is a `def` of type `Prop`.

## Theorems

- `divisionCMQuasiProjectiveRepresentabilityStatement_of_normalSublevel hq hs`.
  The two statements imply `DivisionCMQuasiProjectiveRepresentabilityStatement …`.
  Given `D.IsDivision` and `U`, the Lean proof takes the sublevel `U'` from
  `hs` and applies `hq` to it.
- `divisionCMNormalSublevelRepresentabilityStatement_of_quasiProjective hrep`.
  The premise implies the normal-sublevel statement. The Lean proof takes
  `U' = U`. Normality of `U.obj.subgroup.subgroupOf U.obj.subgroup` follows
  by rewriting with Mathlib's `Subgroup.subgroupOf_self` to the top subgroup,
  which is normal.
- `divisionCMQuasiProjectiveRepresentabilityStatement_iff_normalSublevel hq`.
  Under the normal-quotient statement, the premise and the normal-sublevel
  statement are equivalent. The proof combines the two theorems above.
- `divisionCMRepresentabilityStatement_of_normalSublevel hq hs hlift hval`.
  The normal-quotient statement, the normal-sublevel statement, and the
  published `DivisionCMArtinianLiftingStatement` and
  `DivisionCMDiscreteValuativeExistenceStatement` together imply
  `DivisionCMRepresentabilityStatement …`. The proof applies the published
  `divisionCMRepresentabilityStatement_of_premiseStatements` to the first
  theorem's result.

## Why this split

A general small level need not itself be a level at which an ordinary
polarized moduli scheme is expected, such as a level inside a principal
congruence level `K(N)`. So some finite quotient step seems unavoidable.
Every small level `U` contains open normal subgroups of finite index inside
any given open subgroup, for example the normal core in `U` of
`U ∩ K(N)`. Representability at such a sublevel must be pushed down to `U`. The normal-quotient
statement isolates this step. It is a statement about the existing
normalized class presheaf at all small levels and does not use the division
hypothesis. The remaining normal-sublevel statement leaves the choice of a
convenient normal sublevel to its prover.

## Expected routes

Neither statement is proved here. The expected routes are informal.

- Normal-quotient statement. Let `Q` be the finite group
  `U.obj.subgroup ⧸ (U'.obj.subgroup.subgroupOf U.obj.subgroup)`. It acts on
  the representing scheme `X'` at `U'` through the existing level-change maps.
  Small-level rigidity (the published, unproved
  `CMSmallLevelRigidityStatement`) should make the action free. A free action
  of a finite group on a quasi-projective scheme over a field has a
  quasi-projective quotient `X'/Q`, and `X' → X'/Q` is a finite étale
  `Q`-torsor. The presheaf at `U` should be the étale quotient of the presheaf
  at `U'` by `Q`. This needs étale-local lifting of level structures and
  étale descent for the normalized classes. Then `X'/Q` represents the
  presheaf at `U`.
- Normal-sublevel statement. Take `U'` normal in `U` and inside a level at
  which the ordinary polarized moduli scheme is available (Task 3449). Then cut out
  the locus of the PEL data, the action, the determinant condition and the
  Rosati condition, and compare it with the normalized class presheaf.

These follow the representability discussion of Kottwitz, *Points on some
Shimura varieties over finite fields* (1992), §5, pp.390–392
(`kottwitz-1992-points-shimura-finite-fields`), in characteristic zero. The
Lean statements are internal and are not transcriptions of statements there.
