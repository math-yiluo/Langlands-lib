# Comparison: from `A^K × Y` to `A^K × S`

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.Clause3`.

An internal module of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`. It proves the
third clause of the target (comparison), following Jantzen 2007 (Lemma 2.1.2) and Mínguez
2009 (§3). Only the mathematics stated in the Lean declarations below is claimed.

## Declarations

* `powerFunctor F T A K`: the functor `Y ↦ A^K × Y` from smooth representations of `GL_m` to
  smooth representations of `GL_(powerRank d K m)`. It is defined by recursion on `K` as the
  composite of `K` functors `Y ↦ (T.binaryNormalizedProductFunctor d _).obj (A, Y)`.
  * `powerFunctor_obj`: its object at `Y` is exactly `powerProduct F T A K Y`.
  * `powerFunctor_preservesFiniteLength`: it preserves finite length, by
    `Derivative.ProductDerivativesFiniteLength.binaryProduct_hasFiniteLength`.
  * `powerFunctor_preservesFiniteLengthShortExact`: it preserves short exact sequences of
    finite-length representations. The Library's `Aubert.binaryProductExactness` provides
    exactness of each step in the second variable.
* `exists_isSubrepresentation_of_isSubrepresentation_castRank`: the comparison step
  `exists_isSubrepresentation_of_isSubrepresentation_binaryProduct` (module `Comparison`)
  for embeddings into a rank transport `castRank h (𝔄 × Y)`. Proof: `subst h`.
* `nonempty_iso_of_isSubquotient_of_isIrreducible`: an irreducible subquotient of an
  irreducible smooth representation is isomorphic to it
  (`CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient`).
* `isSubrepresentation_of_nonempty_iso`: an isomorphism is an embedding.
* `comparison`: the clause itself, stated exactly as in the target. Suppose `Y` has finite
  length and is left `A`-reduced, every irreducible subrepresentation of `Y` is isomorphic
  to the irreducible `S`, and the irreducible `π` embeds into `A^K × Y`. Then `π` embeds
  into `A^K × S`. Proof by cases:
  * `K = 0`: `π` is an irreducible subrepresentation of `Y`, hence `π ≅ S`.
  * `d = 0` (for `K ≥ 1`) is impossible. `Y` is subsingleton
    (`subsingleton_of_leftReduced_rankZero`, module `Product`), hence so is `A^K × Y`
    (`subsingleton_map_of_preservesFiniteLengthShortExact`, module `PieceTools`, applied to
    `powerFunctor`). But `π` is nontrivial and embeds into it.
  * `d > 0`, `m = 0`: by `exists_irreducible_of_isSubquotient_map_of_finiteLength` (module
    `PieceTools`) for the exact functor `powerFunctor`, `π` is a subquotient of `A^K × τ`
    for an irreducible subquotient `τ` of `Y`. Both `τ` and `S` are irreducible
    representations of `GL_0`, so both are isomorphic to the binary product unit
    (`Classification.rankZeroIrreducibleUnitIso`). Hence `π` is a subquotient of `A^K × S`.
    This product is isomorphic to a rank transport of the irreducible cuspidal power
    (`nonempty_powerProduct_rankZero_iso`, module `PowerIso`), so it is irreducible. It
    follows that `π ≅ A^K × S`.
  * `d > 0`, `m > 0`: `A^K × Y ≅ castRank (𝔄 × Y)`, with `𝔄 = A × ⋯ × A` irreducible and
    `A`-pure (`nonempty_powerProduct_iso`, module `PowerIso`; module `PowerSupport`). The
    comparison step gives an irreducible subrepresentation `E` of `Y` with
    `π ↪ castRank (𝔄 × E)`. By hypothesis `E ≅ S`, so `π ↪ castRank (𝔄 × S) ≅ A^K × S`.
