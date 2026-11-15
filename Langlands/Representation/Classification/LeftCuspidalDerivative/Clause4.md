# Uniqueness: irreducible subrepresentations of `A^K × S`

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.Clause4`.

An internal module of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`. It proves the
fourth clause of the target (uniqueness). Let `A` be a supercuspidal representation of
`GL_d` and let `S` be an irreducible left `A`-reduced representation of `GL_m`. Then any two
irreducible subrepresentations of `A^K × S = powerProduct F T A K S` are isomorphic.
This is the uniqueness of the highest left `A`-derivative in Zelevinsky 1980 and Mínguez
2009. Only the mathematics stated in the Lean declarations below is claimed.

## Declarations

* `nonempty_iso_of_isSubrepresentation_of_isIrreducible`: an irreducible smooth
  subrepresentation `π` of an irreducible smooth representation `X` is isomorphic to `X`.
  Proof: the embedding is nonzero because `π` is nontrivial, and a nonzero intertwiner
  between irreducibles is an equivalence (`nonempty_equiv_of_ne_zero`, module `Frobenius`).
* `nonempty_iso_of_isSubrepresentation_castRank_binaryProduct`: the statement
  `nonempty_iso_of_isSubrepresentation_binaryProduct` (module `Uniqueness`) for embeddings
  into a rank transport `castRank h (𝔄 × E)`, `h : a + m = N`. Proof: `subst h`.
* `uniqueness`: the clause itself, stated exactly as in the target for every `d`, `A`, `K`,
  `m`, `S`, `π`, `π'`. Proof by cases.
  * `K = 0`: `A^0 × S = S` is irreducible, so `π ≅ S ≅ π'`.
  * `d = 0` (for `K ≥ 1`) is impossible. A left `A`-reduced finite-length representation is
    then subsingleton (`subsingleton_of_leftReduced_rankZero`, module `Product`), but `S`
    is irreducible, hence nontrivial.
  * `d > 0`, `m = 0`: `A^K × S ≅ castRank (A × ⋯ × A)` (`nonempty_powerProduct_rankZero_iso`,
    module `PowerIso`), which is irreducible (`isIrreducible_cuspidalPower`, module
    `PowerSupport`, and `isIrreducible_castRank`). So `π` and `π'` are both isomorphic to it.
  * `d > 0`, `m > 0`: `A^K × S ≅ castRank (𝔄 × S)` with `𝔄 = A × ⋯ × A`
    (`nonempty_powerProduct_iso`, module `PowerIso`). Here `𝔄` is irreducible and `A`-pure
    (`isPure_cuspidalPower`), so the previous declaration applies with `E = S`.
