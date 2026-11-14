# Galois stability of normal-basis principal-unit sets

Worker 518 adapts M145.005 from Naganori Yamaguchi's
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean`,
lines 126–137, at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The theorem `Langlands.NYLL.LocalClassFieldTheory.galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet`
proves its unchanged published target with suffix `Statement`, applied to
`K L n sigma ha`, retaining its universe, all instances, and the implicit unit binder.

Install the actual integral-closure action on integer-ring units, as in the
statement. Unfold membership in the principal-unit set, so the goal is that
the deviation of the acted-on unit from one belongs to the chosen lattice dilate.
By definitional reduction of the unit action and the published
`LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure_apply`,
the field value of the acted-on unit is the Galois automorphism applied to the
original field value. Apply the lattice-dilate stability theorem M145.004 to
`ha`; preservation of subtraction and one identifies the resulting membership
with the goal.

The only direct imports are the unchanged target module
`NormalBasisGaloisAction.PrincipalUnitStabilityStatement` and the M145.004 proof
`NormalBasisGaloisAction.U004.Proofs`. The unit-action evaluation law
M140.004 and the membership equivalence M144.060 are not needed as separate
proof imports: their relevant equalities are unfolded directly. No private
or duplicate Galois lattice-stability theorem is introduced here.

Modifications: extract this one theorem, prefix the namespace by `Langlands.NYLL`,
use focused imports and the published proposition as the type, and replace the
source simplification through M140.004/M144.060 with the explicit field-value
calculation above. Original copyright and author attribution are retained;
Apache-2.0 `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.

The pinned original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registrations: `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
This is stability under the actual Galois action only; it discharges no host
class-formation or reciprocity target.
