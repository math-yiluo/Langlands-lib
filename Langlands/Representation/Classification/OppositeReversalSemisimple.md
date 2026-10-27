# Opposite induction of an arbitrary Levi representation by block reversal

Module `Langlands.Representation.Classification.OppositeReversalSemisimple`.
It generalizes the tensor-only `Langlands.glOppositeProductReversal`
(`Langlands.Representation.Induction.OppositeProductReversalProof`) from block
tensor products to an arbitrary representation `σ` of the actual product Levi
`B.Levi F.Carrier`. It then derives opposite semisimplicity, *conditionally* on
the tempered upper induction proposition.

## Declarations

- `T.leviReverse B : B.reverse.Levi F.Carrier ≃ₜ* B.Levi F.Carrier` is the
  inverse of the continuous reindexing
  `FiniteTensor.reindexGroupContinuous (fun i => GL (B.size i)) Fin.revPerm`,
  which sends `m` to `i ↦ m i.rev`. So `leviReverse` sends `m'` to the
  `B`-Levi element whose block `i.rev` is `m' i`. The product topology is the
  one induced by `T.topology`.
- `T.oppositeLeviProjection_reverseToOpposite_eq B q`: for `q` in the reversed
  upper parabolic `B.reverse.parabolic`, the actual opposite Levi projection of
  the conjugate `w q w⁻¹` is `leviReverse` of the reversed upper Levi projection
  of `q`. Here `w = B.reverseMatrix F.Carrier`, and
  `B.reverseToOpposite F.Carrier` is the published conjugation isomorphism onto
  `B.oppositeParabolic`. The proof applies the published blockwise identity
  `oppositeLeviProjection_reverseToOpposite`.
- `T.oppositeReversalEquiv B σ` is an equivalence of representations of
  `GL_n(F)`:

  ```
  T.normalizedOppositeParabolicInduced B σ ≃
    T.normalizedParabolicInduced B.reverse (σ.comp (T.leviReverse B).toMonoidHom)
  ```

  It is built from two pieces.
  1. The identity linear map of `W` is an equivalence between two
     representations of `B.reverse.parabolic`. One is the opposite inducing
     representation `δ_P^{-1/2} ⊗ σ ∘ (opposite projection)` pulled back along
     `reverseToOpposite`. The other is the upper inducing representation of
     `B.reverse`, `δ_{P'}^{1/2} ⊗ (σ ∘ leviReverse) ∘ (upper projection)`. The
     moduli agree by the published `oppositeHalfModulus_reverseToOpposite`, and
     the Levi parts agree by the previous lemma.
  2. The published `Induction.conjugateSmoothInducedEquiv w e` transports smooth
     induction along conjugation by `w`. Its inverse is composed with
     `Induction.smoothInducedEquiv` of piece 1.

  As in `glOppositeProductReversal`, the function maps are `f ↦ (x ↦ f (w x))`
  and `h ↦ (x ↦ h (w⁻¹ x))`. Both representations act by right translation on
  their actual function spaces. The equivalence changes the inducing data
  (`B.reverse`, `σ ∘ leviReverse`). It does not identify opposite and upper
  induction of the same `σ`.
- `isSemisimple_normalizedOppositeParabolicInduced_of_temperedInduction h1`:
  assume `h1 : GLTemperedInductionStatement.{uF, uW}`. Take positive `n`, a block
  shape `B`, any Borel measurable structure and Haar measure `μ` on the central
  quotient of `B.Levi`, and an irreducible `σ` on `W : Type uW` with
  `IsTemperedModCenter σ μ`. Then `T.normalizedOppositeParabolicInduced B σ` is
  semisimple.

## Proof of the semisimplicity theorem

1. On `Q' = B.reverse.Levi ⧸ center`, take the Borel σ-algebra and the
   pushforward `μ' = μ.map (centralQuotientCongr φ).symm`, where
   `φ = leviReverse`. This is a Haar measure by
   `ContinuousMulEquiv.isHaarMeasure_map`. Pushing `μ'` forward along
   `centralQuotientCongr φ` gives back `μ` (`Measure.map_map`, `map_id`).
2. The published `isTemperedModCenter_comp_continuousMulEquiv` (the change of
   variables on the central quotient) turns `IsTemperedModCenter σ μ` into
   `IsTemperedModCenter (σ.comp φ) μ'`.
   `CuspidalSupport.isIrreducible_comp_mulEquiv_iff` gives irreducibility of
   `σ.comp φ`.
3. The second component of `h1` at `B.reverse`, `μ'` and `σ.comp φ` gives
   semisimplicity of `T.normalizedParabolicInduced B.reverse (σ.comp φ)`.
4. Semisimplicity of group-algebra modules transfers back along the bijective
   module map of `(oppositeReversalEquiv B σ).symm`
   (`isSemisimpleModule_iff_of_bijective`).

`h1` is an explicit hypothesis and is not proved here. Its proof is owned by
task `fb462a13-96b1-4ac1-a47d-4fd7510d0ac4`.

## Provenance

This is a derived construction. Silberger's Lemma 4.5.15 (printed p. 191,
`silberger-1979-harmonic-analysis`) states complete reducibility for any
parabolic pair. The Library's `GLTemperedInductionStatement` concerns standard
upper block parabolics only. This module supplies the reduction from the
opposite block parabolic to the upper parabolic of the reversed shape. That
reduction is a direct formal construction and not a quoted theorem.
