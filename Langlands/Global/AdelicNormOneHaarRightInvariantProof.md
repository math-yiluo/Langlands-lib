# Right invariance of Haar measure on actual norm-one adelic groups

`Langlands.Global.AdelicGroupPoints.normOneHaarRightInvariant` proves the
existing proposition `NormOneHaarRightInvariantStatement.{u}` at every
universe `u`. For every number field `F : Type u` and every smooth connected
affine group scheme `G` over `F` with its existing locally finite type
interface, the fixed `Measure.haar` on `normOneSubgroup F G` is right
invariant. This includes nonreductive groups. The actual adelic topology,
Borel structures, rational algebraic characters, and subgroup Haar measure
are those of the statement.

The Lean proof applies the published
`normOneHaarRightInvariantStatement_of_local` to the proved universal local
formula `PlaceGroupPoints.localModularCharacterAdjointDeterminant`. No
analytic comparison or right invariance remains as a premise.

The imported argument has three parts:

1. `LocalModularCharacterAdjointDeterminantProof` proves the local analytic
   modular character formula on the actual completion-valued point groups.
   Its charts and derivative comparison identify the analytic conjugation
   determinant with the actual algebraic adjoint determinant. Local Haar
   estimates give an upper bound; the bound at the inverse gives equality.
   The normalized complex-place absolute value is squared.
2. `AdelicLocalModularComparison` assembles this formula on the actual
   adelic group. The modular character on each local insertion is identified
   using its closed normal image and the continuous multiplicative
   equivalence with the original local group. Normalized character norms
   agree on those insertions. Continuity and convergence of finite local
   truncations then identify the two homomorphisms everywhere.
3. `AdelicNormOneModularCharacter` applies the formula to the rational
   adjoint determinant character. Every point of `normOneSubgroup F G`
   lies in its character-norm kernel, since that subgroup is the
   intersection of all rational character-norm kernels. The closed normal
   subgroup comparison identifies the ambient modular character restricted
   to this subgroup with its intrinsic modular character. That character
   is therefore one. The Haar right-translation formula proves right
   invariance of the subgroup's own fixed Haar measure.

The provenance is the composition of these proved Library results, as
implemented by `AdelicHaarUnimodularityReduction`. It realizes the first
assertion of Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Section 3.6, Lemma 3.6.4, printed p.90, using the local formula of
Proposition 3.6.1 and the adjoint determinant character in (3.13).
The original Section 3.6, printed pp.87–90, and all five pages of the
October 2026 author errata were read in this task; the errata contains no
correction to this assertion.

Source records are `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`,
and `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.

This focused proof establishes the entire first conjunct of
`AdelicHaarUnimodularityStatement`. The second conjunct, right invariance
on the full connected reductive adelic group, still requires the
separate reductive determinant-triviality input.
