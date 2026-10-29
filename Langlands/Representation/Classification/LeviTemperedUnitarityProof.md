# Unitarity of analytically tempered actual block Levi representations

Authors: Worker 551 and Worker 560.

`Langlands.glLeviTemperedUnitarity` proves exactly the published closed
proposition `Langlands.GLLeviTemperedUnitarityStatement.{uF,uV}` from
`Langlands.Representation.Classification.LeviTemperedUnitarityStatement`.

For every prime `p`, field `F : PadicField.{uF} p`, supplied topological data
`T`, positive total rank `n` and block shape `B`, the group is the actual
product Levi `M = B.Levi F.Carrier`. Its quotient is by its full center.
Given any supplied Borel measurable-space realization of that quotient,
one supplied Haar measure `μ`, and an irreducible representation `σ` on any
complex carrier `V : Type uV`, `IsTemperedModCenter σ μ` implies
`IsUnitarizable σ`. The independent universes `uF` and `uV`, the supplied
module structures, and the original action and carrier are retained.
The conclusion supplies an actual invariant positive definite Hermitian
form on `V`.

## Implemented proof

1. The temperedness hypothesis includes admissibility and smoothness. Bundle
   the original representation as `S = SmoothRep.of σ ht.1.1`. Apply the
   published `CuspidalSupport.padicLeviAdmissibleFactorization` to obtain
   irreducible admissible block factors `A i`, with carriers in the same
   universe `uV`, and a representation equivalence `e` from `S` to their
   actual external tensor representation.

2. Apply the published `glLeviTemperedHaarExtension` to the original
   hypothesis for `μ`. This gives temperedness for every Borel Haar
   realization of the full Levi central quotient. The application retains
   the source measurable space, Borel witness and Haar witness explicitly
   as `m₀ b₀ μ hμ`, and the target ones as `m₁ b₁ ν hν`.

3. For each target measure `ν`, the published
   `isTemperedModCenter_of_equiv e ν` transfers the resulting analytic
   hypothesis to the actual external tensor action. The reverse implication
   of the published `glBlockTensorTempered` then shows that every factor
   `A i` satisfies `T.IsTempered`.

4. Every block has positive rank by `B.positive i`. Apply the published
   closed ambient theorem `glTemperedUnitarity.{uF,uV}` to each irreducible
   factor. This proves `IsUnitarizable (A i).representation`, with all
   hypotheses supplied by the preceding steps.

5. Choose an `InvariantPositiveForm` for each factor. Apply the published
   `FiniteTensor.invariantPositiveForm` to the actual finite external tensor
   representation. The action used by `B.blockTensor` agrees definitionally
   with this external tensor action.

6. Pull the resulting tensor form back along `e` using
   `InvariantPositiveForm.ofEquiv`. The result is a form for the original
   action `σ` on the original carrier `V`, which proves the conclusion.

The factorization, Haar extension, analytic tensor reflection and positive
forms are supplied by the named closed Library theorems. The final theorem
has no auxiliary premise. The target statement and all imported Lean and
Markdown pairs are preserved.

## Provenance and dependencies

This is a derived assembly of published Library constructions. Worker 551
implemented the factorization and tensor-tempered assembly and the final
closed theorem. Worker 560 supplied the Haar adapter and contributed the
finite tensor positive-form application.

The statement's original source is A. J. Silberger, *Introduction to Harmonic
Analysis on Reductive p-adic Groups* (1979), Corollary 4.5.13, printed p.190
(one-based PDF p.196), applied to the split reductive product Levi. Registered
source: `silberger-1979-harmonic-analysis`, SHA256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
Its short proof invokes Corollaries 1.7.9 and 4.5.11. The implementation here
uses the tensor assembly above, with ambient unitarity imported from
`Langlands.Representation.Classification.TemperedUnitarityProof`.
The analytic work enters through that ambient theorem and the published
Haar and tensor comparison theorems; the proof uses their actual
`IsTemperedModCenter` and `T.IsTempered` interfaces.

The other proof imports are
`Langlands.Representation.Classification.TemperedHaarProof`,
`Langlands.Representation.Classification.BlockTensorTemperedProof`,
`Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof`
and `Langlands.Representation.Tensor.UnitaryProof`. The final assembly
uses no downstream tempered-induction, tempered-exhaustion,
square-integrable block-induction or regular Langlands-classification proof.
