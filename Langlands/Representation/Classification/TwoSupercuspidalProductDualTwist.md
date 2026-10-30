# Smooth dual and `|det|` twist of normalized block products

Authors: Worker 745, with proofs adapted from Worker 264 and Worker 6.
Worker 264 wrote the proof that `productSmoothDual` adapts. Worker 6 wrote the
proof that `productCharacterTwist` adapts, and the three private lemmas, which
are copied verbatim. Worker 745 wrote the rest and did the adaptation. The
section "Reused published proofs" below gives the exact sources.

This module proves the identity
`ν · (ρ_1 × … × ρ_r)~ ≅ ν ρ_1~ × … × ν ρ_r~` for normalized products of
admissible blocks of `GL_n`, where `ν = |det|` and `~` is the smooth
contragredient. It also specializes the identity to two supercuspidal blocks.
It is an input to the proof of Ze80 Proposition 1.11(a) (task
`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`), which follows BZ77 Theorem 4.2.

## Source

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), source `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

- §4.8, proof of Lemma 4.7(b), printed p.455 (PDF p.16): "Set `π̄ = νπ~`;
  according to 2.3 (d) and 1.9 (f), `π̄ = ρ̄_1 × … × ρ̄_r`, where
  `ρ̄_i = ν ρ̃_i`." This is `productDualTwist` below.
- §2.3(d), printed p.446 (PDF p.7): `i_{G,M}(ρ)~ = i_{G,M}(ρ~)`. This is
  `productSmoothDual`.
- §1.9(f), printed p.445 (PDF p.6): a character `χ` of `G` commutes with
  induction. For `χ = |det|^s` this is `productCharacterTwist`.
- §4.2, printed p.454 (PDF p.15): `ν(g) = |det g|`, with the standard norm.

The Lean results specialize the source. `productSmoothDual` and
`productDualTwist` assume that every block is admissible. BZ77 2.3(d) is
stated for all algebraic representations. Here admissibility is needed
because the proof uses the published natural induction duality and the
published surjectivity of the smooth-dual tensor map, and both assume it.
`productCharacterTwist` treats only characters of the form `χ ∘ det` for a
smooth character `χ` of `F^×`. No errata entry for BZ77 is registered in the
project literature index or the public notes.

## Parameters and normalization

`p` is prime, `F : PadicField.{uF} p` and `T : F.TopologicalData` are
explicit. Every statement installs `letI := T.topology`. Blocks live in
`SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)`. The product is
the published normalized product `T.normalizedProductInductionFunctor B`. Its
carrier universe is `max uF uV`. `ν` on `GL_m` is the published
`T.determinantPowerCharacter m 1`, which is `realPowerCharacter
(T.determinantNorm m) 1`, the residue-normalized `|det|`.

## Declarations

Namespace `Langlands.Classification`. The two private lemmas
`determinant_parabolic` and `determinant_leviEmbedding` compute the
determinant of a block upper triangular matrix as the product of the
determinants of its diagonal blocks. They use Mathlib's
`Matrix.BlockTriangular.det_fintype`.

Namespace `Langlands.Classification.ProductDualTwist`:

- `productSmoothDual B δ hadm`: for a block shape `B` of `n` and admissible
  blocks `δ i`, the smooth contragredient of `i_B(δ)` is equivalent, as a
  representation, to `i_B` of the block smooth contragredients. The proof
  composes the published natural normalized induction duality
  (`Parabolic.naturalNormalizedInductionDuality`, applied to the external
  tensor product of the blocks, which is admissible by
  `FiniteTensor.isAdmissible_external`) with the inverse of the smooth-dual
  tensor map. That map is bijective by the published
  `FiniteTensor.smoothDualTensorInjectivity` and
  `FiniteTensor.smoothDualTensorMap_surjective`.
- `productCharacterTwist B χ δ`: for a smooth character `χ` of `F^×`,
  `(χ ∘ det) · i_B(δ)` is equivalent to `i_B((χ ∘ det) · δ_i)`. The proof
  uses the published `Induction.inductionTwist` for the parabolic subgroup.
  It then identifies the twisted inducing representation with the inducing
  representation of the twisted blocks. The private lemma
  `blockTensor_determinant_twist` does this on the Levi subgroup, via the
  published `external_coordinate_twist` and the block determinant formula.
- `absCharacter`: the smooth character `ν = |·|` of `F^×`, defined as
  `realPowerCharacter T.normalizedAbsUnits 1`. Composed with the determinant
  it is `T.determinantPowerCharacter m 1`.
- `productDualTwist B δ hadm`: `ν · i_B(δ)~ ≅ i_B(ν δ_i~)` for admissible
  blocks. It combines `productSmoothDual` with `productCharacterTwist` for
  `absCharacter`.
- `dualTwist ρ`: for a supercuspidal representation `ρ` of `GL_k` (the
  published `SupercuspidalRep`), the supercuspidal representation `ν ρ~`. It
  is the published `SupercuspidalRep.twist` of the published
  `SupercuspidalRep.contragredient`. Closure of supercuspidality under the
  contragredient is the published
  `T.supercuspidalContragredientClosed supercuspidalContragredient`.
- `twoBlockDualTwist hk hl ρ ρ'`: for supercuspidal `ρ` of `GL_k` and `ρ'` of
  `GL_l` (`k, l > 0`),
  `ν · (ρ × ρ')~ ≅ ν ρ~ × ν ρ'~` on `GL_(k+l)`, with the blocks in the same
  order. Here `ρ × ρ'` is the published product of the target statement
  `TwoSupercuspidalNonadjacentProductIrreducible`, that is
  `(T.normalizedProductInductionFunctor (Shahidi.twoBlocks k l hk hl)).obj
  (twoBlockFactors hk hl ρ.obj ρ'.obj)`. Supercuspidal representations are
  admissible, so `productDualTwist` applies. The block families agree
  definitionally, block by block.

All equivalences are `Representation.Equiv`, wrapped in `Nonempty`.

## Reused published proofs

Two proofs in this module come from published Library proofs by other workers.
All locations refer to Library commit
`9076dbdeff7e1d9a1bddd23c2f62e11d180814a1`.

- `productSmoothDual` adapts Worker 264's proof of
  `twistedProductOrdinaryDual`, in
  `Langlands/Representation/Classification/TwistedProductOrdinaryDualProof.lean`,
  lines 52–74. The Lean steps are the same: the external tensor product `σ`,
  the duality `EI`, the bijectivity `hbij` and the equivalence `e2`. The
  adaptation applies them to the blocks `δ i` directly, not to the twisted
  blocks `ν^(s_i) δ_i`. It therefore drops the admissibility-of-twist step and
  the final segment-factor equivalence `e3`.
- `determinant_parabolic`, `determinant_leviEmbedding` and
  `blockTensor_determinant_twist` are copied verbatim from Worker 6's
  `Langlands/Representation/Classification/TwistedProductCharacterTwistProof.lean`,
  lines 15–73. They are private there, so they cannot be imported.
- `productCharacterTwist` adapts Worker 6's proof of
  `twistedProductCharacterTwist` in the same file, lines 78–128. The
  adaptation applies it to the blocks `δ i` instead of the segment factors
  `ν^(s_i) δ_i`. It drops the per-block commutation step `hblock`, and the rest
  of the proof is unchanged.

Worker 745 wrote `absCharacter`, `productDualTwist`, `dualTwist` and
`twoBlockDualTwist`.

## Provenance and dependency audit

The statements follow the cited source passages, with the restrictions noted
above. The proofs are adapters over published Library theorems. Two of them
reuse published proofs, as described in "Reused published proofs".

The direct project imports are
`Classification.TwoSupercuspidalProductStructureStatement` (for
`twoBlockFactors` and the product shape),
`Classification.SupercuspidalContragredient`,
`Classification.SupercuspidalContragredientProof`,
`Parabolic.NaturalInductionDualityProof`,
`Tensor.SmoothDualInjectivityProof`, `Tensor.SmoothDualSurjectivityProof`,
`Induction.Equivalences`, `Category.Contragredient`,
`Induction.BlockCharacterAbsorption` and `Induction.CharacterTwistProof`.
Their transitive `Langlands` closure has 209 modules at Library commit
`9076dbdeff7e1d9a1bddd23c2f62e11d180814a1`. It contains these
`Classification` modules: `Supercuspidal`, `SupercuspidalTwist`,
`SupercuspidalContragredient{,Aux,Proof,Statement}`,
`CuspidalJacquetMultiplicityStatement` and
`TwoSupercuspidalProductStructureStatement`. The last two are statement
modules. Nothing in this module uses their propositions as hypotheses or
consequences. The closure contains no derivative, segment, socle, head,
multisegment, Langlands-classification, square-integrability, tempered,
exhaustion or product-irreducibility module. So no excluded result of task
`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` is used. This audit covers this module
only. It does not certify the dependency closure of a later consumer.
