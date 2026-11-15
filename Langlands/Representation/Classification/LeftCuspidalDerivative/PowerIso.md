# Iterated products with a supercuspidal representation as binary products

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.PowerIso`.

An internal module of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`. The target
statement defines `powerProduct F T A K Y = A × (A × ⋯ × (A × Y))` as an iterated binary
normalized product. This module identifies it with a binary product of the cuspidal power
`cuspidalPower T hd A K h = A × ⋯ × A` (module `PowerSupport`) with `Y`. The statements are
isomorphisms of smooth representations after rank transport (`castRank`). They hold for
`d > 0` and `K + 1 ≥ 1` factors `A`. Only the mathematics stated in the Lean declarations
below is claimed.

## Rank transport helpers

* `nonempty_castRank_iso`: `castRank h` carries isomorphisms to isomorphisms.
* `binaryProduct_castRank_left`, `binaryProduct_castRank_right`: a rank transport of the
  left (right) factor of a binary normalized product equals the rank transport of the
  product (`subst`, then `rfl`).
* `nonempty_iso_castRank_of_equiv_comp`: an equivalence `L ≃ R ∘ reindex (finCongr h)` gives
  `R ≅ castRank h L`. Proof: `subst h`, then `GeneralLinear.reindex_finCongr_rfl`.
* `nonempty_binaryAssocIso`: for `a, b, c > 0`,
  `X × (Y × Z) ≅ castRank (Nat.add_assoc a b c) ((X × Y) × Z)`. This is the Library
  equivalence `Aubert.GradedAssociativityProof.binaryAssocEquiv` passed through the previous
  helper.
* `nonempty_binaryProduct_rankZero_iso`: for an irreducible `S` of `GL_0` and any `X` of
  `GL_n`, `X × S ≅ castRank (n = n + 0) X`. Proof: replace `S` by the binary product unit
  (`Classification.rankZeroIrreducibleUnitIso`). Then use the unit equivalence
  `binaryProductRightUnitEquiv` and `BinaryTensor.liftEquiv`. Finally, restriction along
  `reindex (finCongr (Nat.add_zero n))` is the identity.

## Powers

* `sum_cuspidalDatumOf_rank`: `∑ _i : Fin K, rank(κ_A) = K * d`.
* `nonempty_powerProduct_iso`: for `Y` of positive rank `m`, and any
  `ha : ∑ _i : Fin (K + 1), rank(κ_A) = a` and `h : a + m = powerRank d (K + 1) m`,
  `powerProduct F T A (K + 1) Y ≅ castRank h (cuspidalPower T hd A (K + 1) ha × Y)`.
  The proof is by induction on `K`.
  * Base case: `cuspidalPowerOneEquiv` identifies `A^1` with `A`.
  * Step: the induction hypothesis gives `A × (A^(K+1) × Y)`. Associativity
    (`nonempty_binaryAssocIso`, all three ranks positive) turns this into
    `(A × A^(K+1)) × Y`. Then `nonempty_cuspidalPowerSuccIso` gives `A^(K+2) × Y`.
  * The remaining rank transports are combined with `castRank_trans` (module `Pieces`).
    Transports along equal ranks agree by proof irrelevance.
* `nonempty_powerProduct_rankZero_iso`: for an irreducible `S` of `GL_0`, and any
  `ha : ∑ _i : Fin (K + 1), rank(κ_A) = a` and `h : a = powerRank d (K + 1) 0`,
  `powerProduct F T A (K + 1) S ≅ castRank h (cuspidalPower T hd A (K + 1) ha)`. The proof
  is by induction on `K` and needs no associativity.
  * Base case: `nonempty_binaryProduct_rankZero_iso` and `cuspidalPowerOneEquiv`.
  * Step: `A × castRank (A^(K+1)) = castRank (A × A^(K+1))`, then
    `nonempty_cuspidalPowerSuccIso`.
