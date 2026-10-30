# Upper exponent bounds of `GL_n` on the single-block product Levi

Author: Worker 978. No proof code was adapted from other workers. The route
follows the one-block idiom of the published
`Langlands.Representation.Classification.SquareIntegrableExponentProof`.

`Langlands.glOneBlockUpperExponent` proves exactly the published
`Langlands.GLOneBlockUpperExponentStatement.{uF,uV}` from
`Langlands.Representation.Classification.OneBlockUpperExponentStatement`.
Fix a prime `p`, a finite `p`-adic field `F : PadicField.{uF} p`, its realization
`T`, and `n` with `hn : 0 < n`. Let `V : Type uV` be any complex vector space,
possibly zero, and let `π` be a representation of `GL_n(F)` on `V`. Suppose every
actual normalized standard-upper Jacquet exponent `χ` of `π` along any block
shape `B` satisfies `‖χ a‖ ≤ 1` whenever `i ↦ |a i|` is monotone. Then
`ProductLeviChamber.UpperExponentHypothesis` holds for the one-block shape
`C := CuspidalSupport.LeviAdmissibility.oneBlock n hn` and the representation
`π.comp (ScalarLayer.oneBlockLeviEquiv T hn).toMonoidHom`.

The statement's admissibility hypothesis is not used. The proof adds no
irreducibility, finite length, nontriviality, central character, temperedness,
or comparison hypothesis. Every comparison below is a proved Library theorem.

## The Levi identification

The helper `Langlands.ScalarLayer.oneBlockLeviEquiv_toMonoidHom` proves

```
(ScalarLayer.oneBlockLeviEquiv T hn).toMonoidHom = C.leviEmbedding F.Carrier.
```

Both sides are monoid homomorphisms from the one-block Levi to
`GeneralLinear n F.Carrier`. The proof compares matrix entries. The left side
evaluates a Levi element `m` at its unique block `⟨0, _⟩`. For `C` the length is
`1` by `rfl`, and its sole block index is `C.singleBlockIndex hC`. The block's
inner coordinate map is the identity on `Fin n` by
`GeneralLinear.BlockShape.singleBlock_index_val`. Then
`GeneralLinear.BlockShape.leviEmbedding_apply_same`
for that block shows that entry `(x, y)` of `C.leviEmbedding F.Carrier m` is
entry `(x, y)` of `m` at the sole block.

After rewriting with this equality, the representation is
`π.comp (C.leviEmbedding F.Carrier)`. This is the setting of the published
module `Langlands.Representation.Geometric.SingleBlockJacquetTransport`.

## Transfer of exponents and chambers

Unfold `UpperExponentHypothesis`. Fix a refinement `D` of the sole block, a
flattened scalar character `ψ` with open kernel, and a generalized
eigencharacter occurrence. This occurrence is in the normalized refined Jacquet
module of `π.comp (C.leviEmbedding F.Carrier)`, restricted to flattened block
scalars. Also fix a flattened tuple `a` that is blockwise monotone in normalized
absolute value. Write `B := C.singleBlockRefinementEquiv hC D` for the ordinary
block shape of `GL_n` given by refining the sole block.

1. `PadicField.TopologicalData.singleBlock_isJacquetExponent_iff_flattened`
   turns the open kernel and the generalized occurrence into
   `T.IsJacquetExponent B π χ`. Here
   `χ := ψ.comp (C.singleBlockScalarMulEquiv hC D F.Carrierˣ).symm.toMonoidHom`.
   This published equivalence is built from three proved comparisons.
   `singleBlockRefinedJacquetLinearEquiv` lifts the actual quotient map and sends
   each refined unipotent coinvariant class to the ordinary Jacquet class of
   the same vector. `singleBlock_refinedLeviModulus` identifies the refined
   modulus product with the ordinary modulus of `B`. Both normalized actions use
   the same inverse positive square root, so
   `singleBlockNormalizedRefinedJacquetEquiv` and, on block scalars,
   `singleBlockScalarJacquetEquiv` are representation equivalences.
   `singleBlockScalarMulEquiv` reindexes
   scalar coordinates through the actual `C.flattenBlockEquiv D`. It preserves
   open kernels (`singleBlock_isOpen_ker_iff`) and generalized occurrence with
   one common natural power (`singleBlock_isGeneralizedEigencharacter_iff`).
2. `PadicField.TopologicalData.singleBlockScalar_forall_block_monotone_iff`
   turns blockwise monotonicity of `a` into monotonicity of
   `j ↦ |singleBlockScalarMulEquiv hC D F.Carrierˣ a j|` on the ordinary blocks
   of `B`. There is only one outer block, so the condition is a single
   monotonicity condition, with walls and central directions included.
3. The hypothesis on `π`, applied to `B`, `χ` and the reindexed tuple, gives
   `‖χ (singleBlockScalarMulEquiv hC D F.Carrierˣ a)‖ ≤ 1`. Since `χ` is `ψ`
   composed with the inverse coordinate equivalence, `MulEquiv.symm_apply_apply`
   turns this into `‖ψ a‖ ≤ 1`.

The proof uses only `propext`, `Classical.choice` and `Quot.sound`.
