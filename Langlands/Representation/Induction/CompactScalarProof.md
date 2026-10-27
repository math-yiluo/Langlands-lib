# The scalar compact-picture integral for standard GL parabolics: proof

Author: Worker 235.

`Langlands.glParabolicCompactScalarIntegral` proves the published
`Langlands.GLParabolicCompactScalarIntegralStatement.{uF}` from
`Langlands.Representation.Induction.CompactScalarStatement`. Its type is exactly
that proposition, in the arbitrary field universe `uF`, with no additional
parameters, typeclasses or hypotheses. The module contains only this theorem.
Its two helper modules belong to the same contribution:

- `Langlands.Analysis.Local.ModularCompactAverage`: abstract compact averaging
  of functions that are left covariant by Mathlib's modular character of a
  closed subgroup.
- `Langlands.Group.GL.ParabolicModularCharacter`: Mathlib's modular character
  of a standard block parabolic is the Levi character that scales Haar measure
  on the radical, applied to the Levi projection.

Neither the statement pair nor any pair it imports is changed.

## Route and provenance

The statement's Markdown describes Casselman's route (*Introduction to the
theory of admissible representations of p-adic reductive groups*, draft May 1,
1995, `casselman-1995-admissible-representations`). Theorem 2.4.2 (p. 27)
gives the invariant functional `I_δ` on compact induction of the modulus, and
the proof of Proposition 3.1.3 (pp. 32–33) identifies it with the average over
a good compact subgroup `K` with `G = P K`. The implemented proof does not
construct `I_δ`, a quotient measure on `P \ G` or a disintegration of Haar
measure. It proves the invariance of the compact average directly, by a
double-integral argument on `G × P` (`ModularCompactAverage`). The only
GL-specific inputs are:

1. `G = P K` for `K = GL_n(O_F)` (the Iwasawa factorization);
2. a right-invariant Haar measure on `G` that gives `K` mass one;
3. the identification of the full block modulus `T.leviModulus B` with
   Mathlib's modular character of `P` (`ParabolicModularCharacter`).

## Proof

Introduce `p`, `F`, `T`, the rank `n`, the hypothesis `0 < n` and the block
shape `B`. Since `n > 0`, write the rank as `n' + 1`. Install the structures
of `T`: the field topology `T.topology`, `T.valuativeRel`, `T.localField` and
`T.fieldT2`, together with the topological group, local compactness and
second countability of `GL_(n'+1)(F)` (`T.generalLinearTopologicalGroup`,
`T.generalLinearLocallyCompactSpace`, `T.generalLinearSecondCountableTopology`).
Also install local compactness of the parabolic
(`T.parabolicLocallyCompactSpace B`).

**The subgroup and the factorization.** Take
`K = Conductor.levelOpenSubgroup F.Carrier n' 0`, the level-zero open subgroup
`GL_(n'+1)(O_F)`. It is compact by `Conductor.isCompact_levelOpenSubgroup`.
Let `g` be any element. `GeneralLinear.Iwasawa.exists_mul_upperTriangular`
gives `k` in `Iwasawa.integralRange v (n'+1)` with `g k` upper triangular.
`Iwasawa.integralRange_succ` and `Conductor.levelSubgroup_zero` identify that
range with `K`. `BlockShape.mem_parabolic_of_isUpperTriangular` puts `g k` in
`P`. Hence `g = (g k) k⁻¹` with `g k ∈ P` and `k⁻¹ ∈ K`. This gives the
factorization clause of the statement and the hypothesis `G = P K` of the
averaging theorem.

**The measure.** Give `G` its Borel structure. Let
`μ = RankinSelberg.generalLinearHaar F.Carrier n'`. It is a Haar measure
(`generalLinearHaar_isHaar`) and is right invariant by the instance
`generalLinearHaar_isMulRightInvariant`, whose proof is
`RankinSelberg.generalLinearHaarRightInvariant`. It gives `K` mass one
(`generalLinearHaar_integralSubgroup` and `levelSubgroup_zero`). The statement
puts `borel K` on `K`. Because `G` is a Borel space, this equals the subspace
structure (`Subtype.borelSpace`), and the goal is rewritten with that
equality. The witness is `κ = μ.comap Subtype.val`. It is a Haar measure on
`K` by `IsHaarMeasure.comap` applied to the open embedding `K.subtype`.
`comap_subtype_coe_apply` gives `κ univ = μ K = 1`, so `κ` is a probability
measure.

**Integrability.** Let `φ` be locally constant, so it is continuous. Then
`k ↦ φ (k g)` is continuous on the compact space `K`, so it has compact
support and is integrable.

**Invariance.** By `BlockShape.modularCharacter_eq` (from
`ParabolicModularCharacter`) with
`δ = T.leviModulus B` and `hδ = glBlockModulusHaar p F T (n'+1) B`, Mathlib's
modular character of `q ∈ P` is `T.leviModulus B (B.leviProjection F.Carrier q)`.
So the covariance hypothesis of the statement, which uses this full modulus
and not its square root or its inverse, becomes
`φ (q x) = modularCharacter q · φ x`.
`ModularCompactAverage.setIntegral_mul_right_eq` applies with `μ`, the closed
subgroup `P` (`BlockShape.isClosed_parabolic`), the compact open subgroup `K`,
the factorization above and the continuous function `φ`. It gives
`∫ x in K, φ (x g) ∂μ = ∫ x in K, φ x ∂μ`. `integral_subtype_comap` turns both
set integrals into integrals over `K` against `κ`, which is the required
identity.

## Reuse and scope

The proof reuses `Iwasawa.exists_mul_upperTriangular`,
`BlockShape.mem_parabolic_of_isUpperTriangular`, `Iwasawa.integralRange_succ`,
`Conductor.levelSubgroup_zero`, `RankinSelberg.generalLinearHaarRightInvariant`
(through its instance) and `glBlockModulusHaar`, as the task asks. It takes
compactness of `K` from `Conductor.isCompact_levelOpenSubgroup` rather than
from `Parabolic.isCompact_integralRange`, and does not use
`Parabolic.quotientMap_image_integralRange`. One-block shapes, every prime,
every `F : PadicField.{uF} p` and every realization `T` are covered without
case distinctions.

This theorem proves only the scalar statement. It does not establish
normalized-induction unitarity, induction duality, refined Levi integration or
any statement about induced representations or their smooth duals.
