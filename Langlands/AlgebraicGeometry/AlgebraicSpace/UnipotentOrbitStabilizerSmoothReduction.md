# Smooth stabilizers of unipotent actions, from SGA 3 VI_B 4.4 and Milne 14.15

Author: Worker 4246.

This module proves that the published
`Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitStabilizerSmoothStatement.{u}`
follows from two published statements:

- `Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement.{u}`
  (`Langlands/GroupScheme/ReducedBaseSmoothStatement.lean`): SGA 3, Exposé VI_B,
  Corollaire 4.4, over a reduced locally Noetherian base with connected fibres. A group scheme
  locally of finite type whose fibres are smooth, connected and of locally constant dimension
  is smooth;
- `Langlands.GroupScheme.CharZeroUnipotentConnectedStatement.{u}`
  (`Langlands/GroupScheme/Unipotent/CharZeroConnectedStatement.lean`): Milne, Corollary 14.15,
  an affine unipotent algebraic group over a field of characteristic zero is connected.

## The declaration

`unipotentOrbitStabilizerSmooth_of_reducedBase_of_charZeroConnected` is a `def` with
`linter.defProp` disabled, following the Library convention for reductions (for example
`rationalCuspidalJacquetFactorExtractionOfSpecialVertexInputs`). Its type is

```
ReducedBaseConnectedFibreSmoothStatement.{u} → CharZeroUnipotentConnectedStatement.{u} →
  UnipotentOrbitStabilizerSmoothStatement.{u}
```

It assumes nothing else: the inspection reports only the axioms `propext`, `Classical.choice`
and `Quot.sound`. Once both hypotheses are proved, applying this declaration to the two
proofs proves the target.

## The proof

Let `k`, `G`, `Z`, `b` and `d` be as in the target statement, and write `σ` for the projection
`(stabProj b).left` of the stabilizer scheme to `Z.left`. This is the morphism in the
conclusion of the target. The helper module
`Langlands/GroupScheme/SchemeActionStabilizer.lean` (namespace
`Langlands.GroupScheme.ActionStabilizer`, opened in this module) supplies the group scheme
`stabilizerGroup b` over `Z.left`, whose structure morphism is `σ` by definition.

1. **Fibres.** Fix a point `z` of `Z` and write `K` for its residue field and
   `q : Spec K ⟶ Z.left` for the canonical morphism. The composite `q ≫ Z.hom` is `Spec.map φ`
   for a ring map `φ : k ⟶ K` (`Spec.map_surjective`), which makes `K` a `k`-algebra. `K` has
   characteristic zero, because `algebraMap k K` is injective and `k` has characteristic zero.
   Let `G_K` be the base change of `G` along `Spec.map (algebraMap k K)`, and `E` the base
   change of `stabilizerGroup b` along `q`. The structure morphism of `E` is
   `σ.fiberToSpecResidueField z`, and its underlying scheme is the fibre `σ.fiber z`.
   - `G_K` is affine and locally of finite type (base changes of `G → Spec k`), and unipotent
     by the Library theorem `unipotentFieldExtensionStatement` (Milne 14.9).
   - `fibreHom b q _ : E ⟶ G_K` is a closed subgroup (`isClosedSubgroup_fibreHom`; `Spec K`
     has one point). Hence `E → Spec K` is affine and locally of finite type, as the closed
     immersion followed by `G_K → Spec K`.
   - `E` is unipotent by the Library theorem `unipotentClosedSubgroup` (Milne 14.7).
   - `E` is smooth over `K` by the Library theorem `affineCartierSmooth` (Cartier's theorem,
     Milne 3.23), and its underlying space is connected by the hypothesis
     `CharZeroUnipotentConnectedStatement`.

   So every fibre `σ.fiber z` is smooth over `κ(z)` and connected.
2. **Constant dimension.** `HasOrbitDimension b z d` says
   `dim G = dim σ.fiber z + d` in `WithBot ℕ∞`. Adding a natural number is injective there
   (Mathlib's `ENat.WithBot.add_natCast_cancel`), so `dim σ.fiber z` does not depend on `z`.
   A constant function is locally constant.
3. **Conclusion.** `Z.left` is reduced by hypothesis and locally Noetherian, being locally of
   finite type over the field `k` (`LocallyOfFiniteType.isLocallyNoetherian`). `σ` is locally
   of finite type (instance in the helper module). The hypothesis
   `ReducedBaseConnectedFibreSmoothStatement` applied to `stabilizerGroup b` gives
   `Smooth σ`, which is the conclusion of the target.

## Relation to the sources

This is the derivation in the Markdown of `UnipotentOrbitStabilizerSmoothStatement`
(steps 1–4), with two differences. The fibre `H_z` is shown to be a closed subgroup of
`G_{κ(z)}` directly: it is the base change, along the orbit map `g ↦ g.z`, of the rational
point `z` of `Z_{κ(z)}`, which is a closed immersion. The source instead cites Milne,
Proposition 1.41. The remaining inputs are the Library proofs of Milne 3.23, 14.7 and 14.9 and
the two hypotheses above (SGA 3 VI_B 4.4 and Milne 14.15). The declaration name is the
project's (provenance: derived).
