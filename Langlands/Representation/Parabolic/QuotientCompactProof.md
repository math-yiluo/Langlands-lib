# Compactness of the actual block parabolic quotient

Authors: Worker 182 and Worker 206.

This module proves the published proposition
`Langlands.Parabolic.ParabolicQuotientCompactClause` from
`Langlands.Representation.Parabolic.GeometricPrerequisitesStatement`.
For every prime `p`, every `F : PadicField.{uF} p`, every supplied compatible
`T : F.TopologicalData`, every rank `n` and every `B : BlockShape n`, the actual
quotient `Induction.LeftQuotient (B.parabolic F.Carrier)` is compact with the
quotient topology induced by `T.topology`. The field universe is unrestricted.
Rank zero is included. The quotient points are right cosets `P g`, where
`P = B.parabolic F.Carrier`; the name `LeftQuotient` records left covariance.

## Implemented proof

The imported `Langlands.Group.GL.TriangularParabolic` module supplies
`BlockShape.index_lt_index_of_block_lt`, the shared consecutive-coordinate
ordering lemma. It compares prefix sums of positive block sizes to show that
every coordinate of an earlier block precedes every coordinate of a later
block. The same module now contains the existing public helper
`GeneralLinear.BlockShape.mem_parabolic_of_isUpperTriangular`, with its statement
unchanged. That helper combines the ordering with `BlockShape.mem_parabolic_iff`
over any commutative ring.

The compactness assembly works under `T.topology` and `T.valuativeRel`, with
`v = ValuativeRel.valuation F.Carrier` and
`K = Langlands.GeneralLinear.Iwasawa.integralRange v n`, the integral group
`GL_n(O)` in every rank.

1. `Langlands.Parabolic.isCompact_integralRange` proves `K` compact. In rank `0`,
   `GL_0(F)` has exactly one element, so every subset is compact. For rank
   `m + 1`, `Iwasawa.integralRange_succ` identifies `K` with
   `integralSubgroup v.integer m`. By `Conductor.levelSubgroup_zero` this is the
   underlying set of `Conductor.levelOpenSubgroup F.Carrier m 0`, and
   `Conductor.isCompact_levelOpenSubgroup` proves that set compact. The proof
   applies that theorem with the instances `T.topology`, `T.valuativeRel` and
   `T.localField`, so the topology used is exactly `T.topology`.
2. `Langlands.Parabolic.quotientMap_image_integralRange` proves that the image
   of `K` under `Induction.quotientMap (B.parabolic F.Carrier)` is `Set.univ`.
   Given `g`, the published `Iwasawa.exists_mul_upperTriangular v n g` gives
   `k ∈ K` with `g k` upper triangular. That theorem holds in every rank,
   including `0`. The helper above gives `g k ∈ P`. Then `k⁻¹ ∈ K`, and `k⁻¹` and
   `g` are related by `QuotientGroup.rightRel P`, because
   `g (k⁻¹)⁻¹ = g k ∈ P`. So the class of `g` is the image of `k⁻¹`; this is the
   decomposition `G = P K`.
3. The closing theorem `Langlands.Parabolic.parabolicQuotientCompact` has type
   exactly `ParabolicQuotientCompactClause F T B`. The quotient projection is
   continuous (`continuous_quotient_mk'`). By step 2, `Set.univ` is the image of
   the compact set `K` from step 1, so it is compact and the quotient is a
   compact space. The closing theorem assumes no quotient compactness, no
   Iwasawa factorization, no positive rank and no replacement subgroup.

## Original sources and scope

The following original pages were read directly from the registered retained PDFs.

- Bill Casselman, *Introduction to admissible representations of p-adic groups*,
  Chapter III, revision April 29, 2019, Section 1, page 1. It uses compactness of
  `P \ G` and discusses compact open subgroups `K` satisfying `G = P K`.
  Source ID `casselman-2019-jacquet-module`, SHA256
  `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
  where F is a non-Archimedean local field*, Russian Math. Surveys 31:3 (1976),
  Lemma 3.6(b), printed/PDF page 30. This states `G = P Γ` and compactness modulo
  `P`, reducing the assertion to the upper triangular case and invoking Iwasawa
  decomposition. Source ID `bernstein-zelevinsky-1976-representations-gln`, SHA256
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), Section 2.3, printed page 446
  (PDF page 7). Compactness of `G` modulo the parabolic `P` is one of the
  geometric inputs used there for parabolic induction. Section 2.2 on the same
  page identifies the standard Levi subgroups of `GL_n` with ordered partitions.
  Source ID `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

The formal proof specializes these compactness statements to standard block
parabolics of actual general linear groups over the Library's finite extensions
of `Q_p`. The consecutive-index and quotient-image arguments are internal derived
proof details. The algebraic reduction is imported from the published
`Langlands.Representation.Whittaker.Iwasawa` module, whose paired Markdown explains
its internal column-reduction proof and Shintani provenance. No new Iwasawa proof
or additional geometric premise is introduced here.

This result alone does not assert the unipotent exhaustion clauses in the
geometric statement module or admissibility of parabolic induction.
