# The BZ77 4.2 core applied to two supercuspidal blocks

Author: Worker 745. Helper module of the proof of Ze80 Proposition 1.11(a),
first conjunct (task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`).

## Main theorem

`nonadjacent_of_twoBlockDerivativePieces hE hPL hHP hLP :
TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T` proves the
published target from four hypotheses:

- `hE : GeneralLinearDerivativeExactnessStatement.{uF, max uF uV} F T`;
- `hPL : MirabolicDerivativeDetection.{uF, max uF uV} F T`;
- `hHP : MirabolicHighestDerivativePairingStatement.{uF, max uF uV, max uF uV}
  F T`;
- `hLP : TwoBlockDerivativePieces.{uF, uV} F T`, the intermediate proposition
  defined here (see below).

The universe `max uF uV` is the carrier universe of the product `ρ × ρ'`.
`NonadjacentLeibnizPieces` proves `hLP` from the Leibniz filtration and
supercuspidal-derivative statements, and the final module
`TwoSupercuspidalNonadjacentIrreducibilityProof` discharges every hypothesis
with a published proof.

The target is Ze80 Proposition 1.11(a), first conjunct (Zelevinsky 1980,
`zelevinsky-1980-induced-ii`, printed p.175, PDF p.12): for supercuspidal `ρ`
of `GL_k` and `ρ'` of `GL_l` with `[ρ'] ≠ ν[ρ]` and `[ρ] ≠ ν[ρ']` as
rank-indexed classes, `ρ × ρ'` is irreducible. Ze80 cites BZ77 Theorem 4.2
(Bernstein and Zelevinsky 1977, `bernstein-zelevinsky-1977-induced-i`,
printed p.454). The Lean proof follows the BZ77 §§4.7–4.8 argument, as
described in `NonadjacentAssembly.md`.

## The intermediate proposition `TwoBlockDerivativePieces`

For every `ψ`, `k > 0`, `l`, supercuspidal `ρ` of `GL_k` and `ρ'` of
`GL_(l+1)`, with `π = twoBlockProduct ρ ρ'` on `GL_(k+l+1)`:

1. the top derivative of `π` (order `k+l+1`) has `finrank ℂ = 1`;
2. for every `0 < d < k+l+1`, the `d`-th derivative of `π` (as
   `restrictedDerivative`) has an actual filtration (`ObjectRepFiltration`)
   whose graded pieces are each zero, or equivalent to the rank cast of `ρ`
   (possible only if `k = k+l+1-d`, that is, `d = l+1`), or equivalent to the
   rank cast of `ρ'` (possible only if `d = k`).

Provenance: this is the consequence of the BZ77 Leibniz rule (Lemma 4.5 and
Corollary 4.14(c); printed p.455: `(ρ × ω)^(k)` "is glued from
`ρ^(i) × ω^(k-i)`, `i = 0, …, k`") and of BZ77 4.4 (printed p.454: for
cuspidal irreducible `ρ` of `GL_n`, `ρ^(k) = 0` for `0 < k < n` and
`ρ^(n) = 1`) that the argument consumes. With supercuspidal factors only three
pieces survive: `(i, j) = (k, 0)` gives `1 × ρ' ≅ ρ'` at `d = k`, `(0, l+1)`
gives `ρ × 1 ≅ ρ` at `d = l+1`, and `(k, l+1)` gives the one-dimensional
representation of `GL_0` at `d = k+l+1`. It is an internal proposition of this
proof, proved in `NonadjacentLeibnizPieces` (`twoBlockDerivativePieces_of_leibniz`).

## Declarations

Namespace `Langlands.Classification.NonadjacentAssembly`.

- `PieceIn S Φ X`: `X` is zero or equivalent to the rank cast of `Φ A` for a
  supercuspidal `A` whose rank-indexed class lies in `S`.
- `length_eq_zero_of_pieceIn S hS X Y hX hY`: if no class in `S` is the
  `ν`-twist of a class in `S`, then a piece built from `S` (with `Φ = id`) and
  a piece built from `S` with `Φ = dualTwist` carry no nonzero invariant form.
  This uses `twist_class_eq_of_length_ne_zero`.
- `twoBlocksSucc`, `twoBlockProduct`, `twoBlockProductRaw`: the shape
  `Shahidi.twoBlocks k (l+1)` and the product `ρ × ρ'`, that is
  `(T.normalizedProductInductionFunctor (Shahidi.twoBlocks k (l+1) hk hl)).obj
  (twoBlockFactors hk hl ρ.obj ρ'.obj)`, with the rank written `k + l + 1`
  (and `k + (l+1)` in the `Raw` form of the target). The two forms are
  definitionally equal. The proof keeps one syntactic rank form and bridges
  the two by an `rfl` equation of objects, because unifying structured terms
  across the two forms is very slow.
- `isIrreducible_rankCast`, `zeroOrIrreducible_of_pieceIn`, `pieceIn_of_equiv`,
  `pieceIn_of_twoBlock`: elementary closure properties of pieces.
- `twoBlockDualTwistSucc`, `twoBlockDualTwistIso`:
  `ν (ρ × ρ')~ ≅ ν ρ~ × ν ρ'~` in the `k + l + 1` rank form. They come from
  the published `ProductDualTwist.productDualTwist` and are packaged as a
  `SmoothRep` isomorphism via `SmoothRep.mkIso`.
- `piecesWithoutForms_twoBlock hLP ψ hk ρ ρ' h1 h2`: under `hLP` and the
  nonadjacency hypotheses, `PiecesWithoutForms` holds for `ρ × ρ'`. Take
  `S = {[ρ], [ρ']}`. `hS` holds by `sigma_ne_twist` (integral twist freeness)
  on the diagonal and by `h1`, `h2` off it. The filtration for `ν π~` comes
  from `hLP` applied to `(ν ρ~, ν ρ'~)`, transported along the derivative of
  `twoBlockDualTwistIso` (published `LengthTwo.transport` and
  `ObjectRepFiltration.equivTransportGradedEquiv`).
- `nonadjacent_of_twoBlockDerivativePieces`: writes `l = l' + 1`, obtains `ψ`
  from the published `padicUnitaryAdditiveCharacterExists`, and applies
  `irreducible_of_pieces` with the top-derivative clause of `hLP` and
  `piecesWithoutForms_twoBlock`.

## Provenance and dependency audit

All proofs here are original to this module. The only direct import is
`NonadjacentSpecialization`; see its Markdown for the audit of its closure.
No segment, socle, head, multisegment, classification, square-integrability
or product-irreducibility result is imported or used.
