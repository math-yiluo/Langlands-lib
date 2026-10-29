# Prescribed weakly critical discrete-series opposite support: proof

Author: Worker 322.

This module proves the published proposition
[`Langlands.GLWeaklyCriticalDiscreteSeriesSupportStatement`](WeakCriticalStatement.md)
without additional hypotheses:

```text
theorem Langlands.glWeaklyCriticalDiscreteSeriesSupport :
    GLWeaklyCriticalDiscreteSeriesSupportStatement.{uF, uV}
```

The field universe `uF` and source carrier universe `uV` remain independent.
For every prescribed weakly critical exponent `χ` at the standard block pair,
the constructed representation `S : Rep.{uV} ℂ (B.Levi F.Carrier)` is an actual
opposite Jacquet class exponent with scalar character exactly `χ`. It is
square-integrable modulo the full Levi center for every Borel Haar realization,
and the source embeds into its normalized opposite parabolic induction.
The target statement and its imported definitions are used unchanged.

## Implemented proof

The helpers in `Langlands.WeakCriticalSupport` construct the same quotient
throughout the proof.

First, `standard_pullbackRep` identifies the standard-pair pullback with the
original representation by conjugation by one. Thus the unitary dual exponent
contained in weak criticality is an exponent in the original coordinates.
A nonzero dual eigenspace lies in its generalized character space, so the
uniform nilpotence index cannot be zero. The published
`Langlands.glDualJacquetFiniteness` makes this index finite, using source
irreducibility and the admissibility contained in analytic temperedness.
`ENat.lift` therefore supplies a natural number `d > 0` with exact index `d`.

The published `Langlands.dualCharacterMaximalLayer` then supplies a block
scalar `a` for which the actual image `W` of `D_a^(d - 1)` in the character
quotient is nonzero. It also proves that block scalars act on this image
through `χ`. No arbitrary tempered constituent replaces this selected image.

Each defect image is a quotient of the whole normalized opposite Jacquet
module through `dualJacquetCharacterDefectRangeMap`. Source irreducibility
implies finite generation over the full source group algebra. The published
`Langlands.Parabolic.oppositeJacquetFiniteGeneration` transfers this to the
whole opposite Jacquet module, and finite generation passes to the image
along its canonical surjection. Source admissibility passes first to the
opposite Jacquet module and then to the image. The latter step uses the
published fixed-vector surjectivity theorem and compact open subgroups
cofinal among open subgroups of the actual product Levi, using the existing
`Langlands.UnitaryDualJacquetSupport.levi_compactOpen_cofinal` from
[the support adapters](UnitaryDualJacquetSupportAdapters.md). The proof does
not infer finite generation for an arbitrary subrepresentation or for a
restriction to a subgroup.

For a nonzero scalar representation, algebraic dual separation supplies a
nonzero eigenfunctional with the same character. Linearity introduces
neither inversion nor complex conjugation. Applying the published
`Langlands.MaximalConeQuotient.exists_irreducible_quotient` to `W`, with its
admissibility, finite generation, and central block-scalar action, gives an
actual irreducible admissible quotient `S` in the source carrier universe,
with scalar character exactly `χ`. The map `q : W → S` is a surjective
intertwiner for the full Levi.

Composing `q` with the canonical map from the whole opposite Jacquet module
makes `S` a whole-Jacquet quotient. The existing
`Langlands.UnitaryDualJacquetSupport.classExponent_of_quotient` takes the top
subrepresentation to give the subquotient class-exponent witness. Published normalized
opposite reciprocity, via `Langlands.OppositeSupport.quotient_iff_embedding`,
gives an actual injective intertwiner from the irreducible smooth source
into `T.normalizedOppositeParabolicInduced B S.ρ`.

Finally, the published `Langlands.glWeaklyCriticalTopLayerL2` applies to this
same actual quotient of the selected maximal layer. It receives the
original irreducibility, analytic temperedness, prescribed weak criticality,
positive exact index, irreducibility and admissibility of `S`, its scalar
character, and the actual surjection `q`. Its conclusion is exactly the
required square-integrability clause for every Borel Haar measure on the
quotient by the full actual Levi center.

`support_of_layer_inputs` performs this assembly from the two layer
propositions. `support_of_top_layer_l2` discharges the algebraic proposition
using `dualCharacterMaximalLayer`. The closing theorem discharges the
remaining proposition using `glWeaklyCriticalTopLayerL2`. The final theorem
has no theorem-valued assumptions.

## Provenance and scope

The source is Silberger, *Introduction to harmonic analysis on reductive
p-adic groups* (1979), registered as `silberger-1979-harmonic-analysis`,
SHA256 `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
Corollary 4.5.11, printed pp.189–190, supplies prescribed-character
discrete-series support; its maximal-image argument refers back to
Corollary 2.4.2, printed pp.91–92. The PDF page numbers are six larger.
The original passages and the registered errata were checked during
development. The individual algebraic helpers above are internal consequences
of the published constructions. Their proofs use actual Library theorems,
rather than treating a citation or a proposition definition as evidence.
The analytic part is delegated to the imported maximal-layer L² proof;
its implemented index comparison and strict-decay argument are described
in [its Markdown](WeakCriticalTopLayerL2Proof.md).

The full weak-critical predicate retains its strict uniform-nilpotence
comparison over all strictly finer concrete conjugate pairs. The proof
uses no critical-to-minimal equivalence, whole weak-critical refinement
aggregate, ordinary tempered discrete-series support, tempered exhaustion,
tempered unitarity or genericity, regular exhaustion, or equal-exponent
grouping theorem. It assumes no tensor presentation or extra source
unitarity. The quotient construction retains the original carrier universe,
and no Haar normalization is fixed.
