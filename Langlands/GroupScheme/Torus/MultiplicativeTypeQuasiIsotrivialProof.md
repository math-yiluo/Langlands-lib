# Groups of multiplicative type are quasi-isotrivial

`Langlands.GroupScheme.multiplicativeTypeQuasiIsotrivial` proves the statement
`Langlands.GroupScheme.MultiplicativeTypeQuasiIsotrivialStatement.{u}` (Conrad, *Reductive
group schemes*, Appendix B, Proposition B.3.4) in every universe `u`. It covers
every scheme, every henselian local ring and every group of multiplicative type, with no
additional hypotheses. Both parts are proved:

1. a group `H` of multiplicative type over any scheme `S` becomes diagonalizable on every
   member of some étale cover of `S`;
2. over `Spec A` with `A` henselian local, `H` becomes diagonalizable after a finite,
   étale, surjective `S' ⟶ Spec A`.

## Proof

The theorem is
`MultiplicativeTypeQuasiIsotrivial.multiplicativeTypeQuasiIsotrivial_of_pointwise`
(module `MultiplicativeTypeQuasiIsotrivialReduction`) applied to the pointwise
theorem `RelativeMultiplicativeType.IsMultiplicativeType.exists_etale_diagonalizable`
(module `MultiplicativeTypePointwiseSplitting`).

* **Pointwise splitting.** Every point of `S` lies in the image of an étale `U ⟶ S` over
  which `H` is diagonalizable. The free part of the character group is handled by the
  Library's universal subtorus, which is a relative torus and so splits étale-locally. The
  torsion part is handled by the étale scheme of homomorphisms from a finite diagonalizable
  group (`HomScheme.MultiplicativeTargetEtale`) and its open classifying neighbourhood
  (`HomScheme.MultiplicativeTargetClassifying`). The two parts are glued by the split
  criterion `isDiagonalizable_of_split_parts` (`MultiplicativeTypeSplitCriterion`), and the
  affine chart comes from `exists_affine_chart` (`MultiplicativeTypeAffineChart`). See
  `MultiplicativeTypePointwiseSplitting.md` for the steps.
* **Reduction.** The pointwise étale neighbourhoods form an étale cover, which gives part
  (1). For part (2), take such a neighbourhood of the closed point of `Spec A`. The
  Library's `henselianFiniteEtaleRefinement` refines it by a finite étale local
  `A`-algebra `A'`. Then `Spec A' ⟶ Spec A` is finite, étale and surjective, and the
  splitting pulls back to it. See `MultiplicativeTypeQuasiIsotrivialReduction.md`.

Each supporting module has its own Markdown describing its Lean declarations. The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
