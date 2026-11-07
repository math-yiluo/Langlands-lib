# Products of Tadić blocks in Langlands form

Author: Worker 1792. The flattening lemmas repeat, under new names, the private
helpers of the published `Classification.TadicProductClosure` by Worker 1745.
Module `Langlands.Representation.Classification.TadicHeadPieceFactorization`,
namespace `Langlands.Classification`. The theorems take the published
propositions `SpehUnitarizability`, `IrreducibleLanglandsHeadProduct` and
`MultisegmentHeadClassification` as explicit hypotheses where stated; nothing
else is assumed, and there are no axioms or `sorry`.

## A.10(iii) up to a rank

`TadicSocleHeadDuality F T m` is the proposition: for every unitary cuspidal
datum `ρ`, all `n, d > 0`, every `N ≤ m` and every `σ` on `GL_N`, if `σ` is a
Zelevinsky socle of `a(n,d)^ρ` (`tadicMultisegment ρ n d hd`) then `σ` is a
Langlands head of `a(d,n)^ρ` (`tadicMultisegment ρ d n hn`). This is Tadić's
Theorem A.10(iii), `⟨a(n,d)^ρ⟩ = L(a(d,n)^ρ)` (1986, printed p.377), for
`n d deg ρ ≤ m`. It is a proposition definition used as an induction invariant.

- `TadicSocleHeadDuality.mono`, `.zero`: it is monotone in `m`, and it holds for
  `m = 0` since such socles have positive rank.
- `.spehComparison`: it implies Worker 1745's `TadicSocleSpehComparison F T m`
  (rectangular socles of rank at most `m` are Speh representations), by
  `exists_isSpeh_of_isLanglandsHead`.
- `.socleUnitarity`: with `SpehUnitarizability F T` it implies Tadić's `(U^m)`,
  the published `TadicSocleUnitarity F T m`.

## Head-piece products

`HasTadicHeadPieceFactorization m π` says that `π` is isomorphic to a normalized
product `(T.normalizedProductInductionFunctor B).obj σ` in which every `σ i` is a
Langlands head of some multisegment `c` with `IsTadicHeadPiece m c`.

- `hasTadicHeadPieceFactorization_normalizedProduct`: a normalized product of
  head-piece products is a head-piece product. The proof is that of the published
  `hasTadicFactorization_normalizedProduct`: induction in stages
  (`Parabolic.orderedProductRegrouping`) along `BlockShape.flatten`.
- `oneBlockProductIso`, `hasTadicHeadPieceFactorization_of_isLanglandsHead`: the
  normalized product over the one-block shape is its factor (the published
  `QuotientHom.oneBlockInducedEquiv`), so a Langlands head of a head piece is a
  one-block head-piece product.
- `TadicSocleHeadDuality.hasTadicHeadPieceFactorization`: under A.10(iii) up to
  rank `m`, every member of `X_m` (`IsTadicXBlock m`) is a head-piece product. A
  socle `⟨a(n,d)^ρ⟩` of rank `N ≤ m` is a head of `a(d,n)^ρ`, a piece of degree
  `N ≤ m`. A complementary block `ν^α σ × ν^(-α) σ` with `σ = ⟨a(n,d)^ρ⟩` is the
  two-block product of `ν^(±α) σ`, which are Langlands heads of
  `ν^(±α) a(d,n)^ρ` by the proved `multisegmentConstituentRealTwistCompatibility`;
  these are pieces with `|±α| = α ∈ (0, 1/2)`.

## The contradiction

`TadicSocleHeadDuality.not_iso_xBlockProduct`: assume A.10(iii) up to rank `m`,
`IrreducibleLanglandsHeadProduct F T` and `MultisegmentHeadClassification F T`.
Let `ρ` be unitary, `n, d > 0`, and `π` on `GL_(m+1)` a Langlands head of
`a(d,n)^ρ`. Then `π` is not isomorphic to a normalized product of members of
`X_m`. Proof: such a product is a head-piece product `∏ π'_k` with `π'_k` a head
of `c_k`; it is irreducible because `π` is; Corollary A.6(ii) makes it a head of
`∑ c_k`; the classification gives `a(d,n)^ρ = ∑ c_k`; and
`not_sum_tadicHeadPieces` excludes this, since `deg a(d,n)^ρ = m + 1 > m`.
