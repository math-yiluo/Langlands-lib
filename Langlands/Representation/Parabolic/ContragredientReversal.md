# Reversal of irreducible normalized products through contragredients

Author: Worker 375.

## Statements

Throughout, `p` is a prime, `F : PadicField.{uF} p`, `T : F.TopologicalData`,
and `GL_n` carries the topology of `T`.

- `Langlands.Parabolic.nontrivial_of_isIrreducible`: an irreducible
  representation (Mathlib's `Representation.IsIrreducible`) of a monoid over a
  field has a nontrivial carrier.
- `Langlands.Parabolic.gelfandKazhdan_of_topologicalData`: assuming the
  published proposition `GelfandKazhdanContragredientStatement.{uF,uV}`, for
  every positive `N`, every topological-group structure on `GL_N(F)` for the
  topology of `T`, and every admissible irreducible complex representation
  `ρ` of `GL_N(F)` on a carrier in universe `uV`, there is a
  `Representation.Equiv` from `ρ ∘ θ_N` to `smoothContragredient ρ`, where
  `θ_N = GeneralLinear.inverseTranspose N F.Carrier`.
- `Langlands.Parabolic.normalizedProductInduced_reverse_equiv`: let `B` be a
  block shape of positive rank `n` and let `π i` be complex representations of
  `GL_(B.size i)(F)` on carriers `V i` in universe `uV`. Assume

  1. `GelfandKazhdanContragredientStatement.{uF,uV}` and
     `GelfandKazhdanContragredientStatement.{uF,max uF uV}`;
  2. `StandardNaturalInductionDualityClause.{uF,uV}`;
  3. every `π i` is admissible and irreducible;
  4. the normalized product `T.normalizedProductInduced B π` is irreducible;
  5. the normalized product of the reversed family,
     `T.normalizedProductInduced B.reverse (fun i => π i.rev)`, is
     irreducible.

  Then the two normalized products are isomorphic as representations
  (`Nonempty (Representation.Equiv _ _)`).
- `Langlands.Parabolic.normalizedProductInduced_revPerm_equiv`: the same
  statement with the reversed shape written as `B.permute Fin.revPerm` and the
  blocks as `fun i => π (Fin.revPerm i)`. The proof is the previous theorem:
  `Fin.revPerm i` is `i.rev` and `B.permute Fin.revPerm` is `B.reverse` by
  definition. Stating this form separately avoids an expensive definitional
  unfolding at the use site.

The assumptions in items 1 and 2 are Prop-valued published statements, and
both are proved in the Library: item 1 by the theorem
`gelfandKazhdanContragredient`, item 2 by the first component of the theorem
`naturalNormalizedInductionDuality`. They are kept as explicit hypotheses so
that this module imports only the statements; the consumer
`Classification.TwoSegmentHeadCommutationProof` supplies them from those
theorems.
The two carrier universes in item 1 are needed because Gelfand–Kazhdan is
applied once to the blocks (carriers in `uV`) and once to the reversed product
(carrier in `max uF uV`).

## Proof of the reversal

`gelfandKazhdan_of_topologicalData` rewrites the topology of `T` to the
canonical norm topology (`T.topology_eq_canonicalNormTopology`), writes
`N = m + 1`, and repackages the linear equivalence and pointwise
intertwining identity supplied by the Gelfand–Kazhdan statement as a
`Representation.Equiv`.

For the reversal, write `Π = T.normalizedProductInduced B π`,
`Π' = T.normalizedProductInduced B.reverse π'` with `π' i = π i.rev`, and
`θ = θ_n`. The proof composes five intertwining maps of representations of
`GL_n(F)`:

1. `A : Π ∘ θ ≅ I_{B.reverse}(i ↦ π i.rev ∘ θ)`, the product clause
   `normalizedProductInverseTranspose` of the published
   `inverseTransposeProduct` (module `Parabolic.InverseTransposeProductProof`).
   It needs only smoothness of the blocks, which follows from admissibility.
2. `C : I_{B.reverse}(i ↦ π i.rev ∘ θ) ≅ I_{B.reverse}(i ↦ (π i.rev)^∨)`, the
   blockwise equivalence `T.normalizedProductInducedEquiv` (module
   `Induction.BlockEquivalence`) applied to the Gelfand–Kazhdan equivalences
   of the blocks `π i.rev ∘ θ ≅ (π i.rev)^∨`.
3. `IM : I_{B.reverse}(i ↦ (π i.rev)^∨) → I_{B.reverse}((⊗ π')^∨)`, normalized
   induction (`T.normalizedParabolicInducedMap`) of the canonical tensor-dual
   intertwiner `FiniteTensor.smoothDualTensorIntertwiner π'`. It is injective by
   `T.normalizedParabolicInducedMap_injective` (module `Induction.Equivalences`)
   and the published theorem `FiniteTensor.smoothDualTensorInjectivity` (module
   `Tensor.SmoothDualInjectivityProof`), applied to the finite index type
   `Fin B.reverse.length`.
4. `D⁻¹ : I_{B.reverse}((⊗ π')^∨) ≅ (Π')^∨`, the inverse of the equivalence
   supplied by `StandardNaturalInductionDualityClause` at the block tensor
   `Rep.of (B.reverse.blockTensor π')`, which is admissible by
   `FiniteTensor.isAdmissible_external`.
5. `E'⁻¹ : (Π')^∨ ≅ Π' ∘ θ`, the inverse of Gelfand–Kazhdan for `Π'`, which is
   admissible by `normalizedInductionAdmissibility` and irreducible by
   assumption 5.

The composite `Ψ : Π ∘ θ → Π' ∘ θ` is injective, since all factors except `IM`
are equivalences. Because `θ` is an involution
(`GeneralLinear.inverseTranspose_involutive`), the intertwining identity of
`Ψ` at `θ g` is the intertwining identity `Ψ (Π g v) = Π' g (Ψ v)`, so the same
linear map is an intertwining map `Φ : Π → Π'`. The carrier of `Π` is
nontrivial by assumption 4 and `nontrivial_of_isIrreducible`; with injectivity
this gives `Φ ≠ 0`. Mathlib's `Representation.IsIrreducible.surjective_or_eq_zero`
for the irreducible target `Π'` makes `Φ` surjective, and
`IntertwiningMap.ofBijective` turns it into the required equivalence.

The proof uses neither surjectivity of the canonical tensor-dual map nor any
Jordan–Hölder, Grothendieck-group or character argument.

## Provenance

This is an internal assembly; no literature theorem is claimed for it. The idea
is that the inverse-transpose involution reverses the order of the blocks of a
normalized product, while the contragredient commutes with normalized
induction up to the canonical tensor-dual map. With Gelfand–Kazhdan on both
sides this gives a nonzero map between the two irreducible products. The Lean
proof is the composite above, built from published Library constructions. It
takes the published statements `GelfandKazhdanContragredientStatement` and
`StandardNaturalInductionDualityClause` as hypotheses; their published proofs
are supplied by the consumer.
