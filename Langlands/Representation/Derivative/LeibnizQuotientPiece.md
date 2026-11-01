# The differentiated restriction quotient as a Leibniz grade

Author: Worker 984.

BZ77 Corollary 4.14(c) says that the `k`-th derivative of the product `ρ × σ` is glued
from the products `ρ^(j) × σ^(k-j)`. The published statement module
`Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement`
indexes the pieces by the finite set `leibnizIndices a b d` and gives each index `x`
the piece functor `leibnizPiece T ψ a b d x`.

The source proof differentiates the restriction sequence of Proposition 4.13(a),
`0 → (ρ|P) × σ → (ρ × σ)|P → ρ × (σ|P) → 0`. This module treats the last term
`ρ × (σ|P)` for a first factor of positive rank `m + 1`, a second factor of positive
rank `n + 1` and a positive order `d`. On pairs `(A, B)`, with `A` on `GL_(m+1)` and `B`
on `GL_(n+1)`, it considers the composite

```
Q d = restrictionQuotient T m n ⋙ MD (m+n+1) d _ ⋙
        generalLinearRankCast T (_ : (m+n+1) + 1 - d = ((m+1)+(n+1)) - d) ⋙
        SmoothRep.toRep
```

Here `restrictionQuotient T m n` is the published last term of the sequence. It
restricts `B` to `P_(n+1) = mirabolic n`, forms the left mixed product with `A` and
casts the mirabolic rank `(m+1)+n = m+n+1`. The module proves two results about `Q d`:

- for `d ≤ n + 1`, a natural isomorphism from `Q d` to the Leibniz piece at the
  zero-first index `(0, d)`;
- for `0 < d ≤ (m+1)+(n+1)`, every carrier of `Q d` has at most one element. This
  is meant for `n + 1 < d`, where the zero-first index does not exist.

Each result takes, as explicit data, the corresponding instance of BZ77 4.14(a) for
the left mixed product with ranks `m + 1` and `n` (see Hypotheses). The module
introduces no axioms. It does not prove the target statement
`GeneralLinearDerivativeLeibnizFiltrationStatement`, constructs no filtration and
uses no exact sequence.

## Provenance

This content is internal to the formalization (derived). BZ77
(`bernstein-zelevinsky-1977-induced-i`, content SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`), Proposition
4.13(a), printed p.458 (PDF p.19), gives the restriction sequence above. Corollary
4.14(a), on the same page, gives `(ρ × τ)^(i) = ρ × τ^(i)` for a mirabolic
representation `τ` and `i ≥ 1`. With the convention `τ^(i) = 0` for `i` above the
rank of `τ`, which the Library statement `LeftMixedProductDerivativeVanishing` makes
explicit, this includes a vanishing for those orders. The source
derives 4.14(c) from (a), (b) and 4.13(a). In that derivation the quotient term
`ρ × (σ|P)` contributes `ρ × (σ|P)^(k)` by 4.14(a). By §4.3, printed p.454
(PDF p.15), `σ^(k) = (σ|P)^(k)` for `k ≥ 1` and `ρ^(0) = ρ`, so the contribution is
the piece `ρ^(0) × σ^(k)`, and it is zero when `k` exceeds the rank of `σ`.

This module formalizes that step for the actual Lean functors, with the instance of
4.14(a) supplied as data. The identification of `ρ × (σ|P)^(k)` with the zero-first
piece is the published `leibnizZeroFirstSmoothPieceIso`. The rest consists of rank
casts, which are equality eliminations. The module does not use the proposition of
4.13(a) or of 4.14(a).

## Hypotheses

The module does not import `MixedProductDerivativeStatement`, where 4.14(a) is
stated, and uses no proposition definition as a hypothesis. Instead each declaration
takes the needed instance of 4.14(a) as an explicit argument:

- `E`, a natural isomorphism of exactly the shape of the isomorphism in
  `LeftMixedProductDerivativeIso` at `k = m + 1`, `r = n`, `i = d`, `hi = hd`. Given
  a proof `h` of that proposition, `(h ψ (m + 1) n d hd).some` is such an `E`;
- `V`, the vanishing of the order-`d` derivative of every left mixed product with
  ranks `m + 1`, `n`, for one order `d > n + 1`. This is the conclusion of
  `LeftMixedProductDerivativeVanishing` at `k = m + 1`, `r = n`, `i = d`.

So the results are unconditional constructions from that data. They become
statements about the target only when a consumer supplies `E` and `V` from an
accepted, published proof of 4.14(a).

## Imports

- `Langlands.Representation.Derivative.LeibnizZeroFirstPiece` (published, Worker 984):
  `leibnizZeroFirst_rank` and `leibnizZeroFirstSmoothPieceIso`. Through it, the module
  uses `leibnizPiece` and `leibnizZeroFirstIndex` and the published
  `generalLinearRankCast` with its lemma `generalLinearRankCast_trans` (`Iteration`),
  `mirabolicDerivativeOfOrder` (`Homogeneity`) and `mirabolicRankCastDerivativeIso`
  (`RankCastCompat`, Worker 593 with Worker 984 as coauthor).
- `Langlands.Representation.Derivative.MirabolicProductRestrictionStatement`
  (published): the definition `MirabolicProductRestriction.restrictionQuotient` only.
  The module's proposition `MirabolicProductRestrictionStatement` is not used.

The module does not change these modules.

## Import closure and dependency audit

At Library base `4bec44eec4c7f23def3d25d5c43f4f2a034af469`, a recursive scan of the
`import Langlands.…` lines gives exactly these 81 modules in the transitive project
closure, not counting this module. Each has a nonempty paired Markdown file:

- `Langlands.Group`: `GL.Basic`, `GL.BlockModulus`, `GL.Blocks`, `GL.Mirabolic`, `GL.MirabolicMixedProductSubgroups`, `GL.MirabolicOppositeIntersection`, `GL.MirabolicProjection`, `GL.MirabolicRadical`, `GL.Nonarchimedean`, `GL.NonarchimedeanStatement`, `GL.NormalizedCharacter`, `GL.OppositeBlocks`, `GL.Padic`, `GL.PadicBlocks`, `GL.RankMaps`, `GL.RankReindex`, `GL.UpperUnipotent`.
- `Langlands.HarmonicAnalysis`: `Basic`.
- `Langlands.LocalField`: `Canonical`, `Definitions`, `Normalization.Definitions`, `Normalization.Proof`, `Normalization.Statement`, `Topology`.
- `Langlands.Representation.Category`: `Basic`, `Subquotients`, `Twist`.
- `Langlands.Representation.Derivative`: `GeneralLinearDerivativeLeibnizFiltrationStatement`, `Homogeneity`, `Iteration`, `LeibnizIndices`, `LeibnizPieceCompat`, `LeibnizZeroFirstPiece`, `MirabolicCharacter`, `MirabolicMinus`, `MirabolicProductRestrictionStatement`, `RankCastCompat`, `RightMixedProductDerivativeFiltrationStatement`.
- `Langlands.Representation.Dual`: `Definitions`.
- `Langlands.Representation.Filtration`: `Definitions`.
- `Langlands.Representation.Induction`: `BinaryProduct`, `BlockFactors`, `Definitions`, `Parabolic`.
- `Langlands.Representation.Jacquet`: `Coinvariants`, `Localization`, `PositiveCharacter`, `SmoothTwist`.
- `Langlands.Representation.MatrixCoefficient`: `Definitions`, `LawsProof`, `LawsStatement`.
- `Langlands.Representation.Mirabolic`: `MixedProducts`.
- `Langlands.Representation.Smooth`: `Admissibility.CofinalProof`, `Admissibility.CofinalStatement`, `Definitions`, `SmoothPart.BasicProof`, `SmoothPart.BasicStatement`, `SmoothPart.Definitions`, `Transfer.PullbackProof`, `Transfer.PullbackStatement`, `Transfer.SubquotientProof`, `Transfer.SubquotientStatement`.
- `Langlands.Representation.Tensor`: `Finite`, `OneFactor`.
- `Langlands.Representation.Twist`: `AdmissibilityProof`, `AdmissibilityStatement`, `AlgebraProof`, `AlgebraStatement`, `ContinuousCharacterProof`, `ContinuousCharacterStatement`, `Definitions`, `RealPower`, `SmoothProof`, `SmoothStatement`, `SubquotientDefinitions`, `SubquotientProof`, `SubquotientStatement`.
- `Langlands.Representation.Whittaker`: `Algebraic`, `GeneralLinear`.
- `Langlands.Topology`: `CompactNormCharacter`, `Nonarchimedean.Subgroup`.

These are the 79 modules of the published `LeibnizZeroFirstPiece` closure, together
with `LeibnizZeroFirstPiece` and `MirabolicProductRestrictionStatement`. The imports of
`MirabolicProductRestrictionStatement` (`Homogeneity`, `Induction.BinaryProduct`,
`Mirabolic.MixedProducts`) are already in that closure.

A case-insensitive text scan of the closure finds no Lean file that mentions
segments, socles, classification, exhaustion, supercuspidals or finiteness. The only
mention of finite length is the definition `HasFiniteLength` in
`Representation.Category.Basic`, which this module does not use. In particular, the
closure contains neither `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`,
`IrreducibleCoinvariantFinitenessStatement` nor
`LeviCuspidalCoinvariantFinitenessStatement`. It contains no module of the excluded
segment, two-supercuspidal or classification tasks. It contains no proof module of
4.13(a), no exactness module and no `MixedProductDerivativeStatement`. The two
`Whittaker` modules only define additive characters, Whittaker functionals and
function models, with elementary lemmas about them.

The proofs use only the following inputs:

- the definitions `restrictionQuotient`, `leibnizPiece`, `leibnizZeroFirstIndex`,
  `mirabolicDerivativeOfOrder`, `mirabolicRankCast`, `generalLinearRankCast` and
  `T.leftMixedProductFunctor`;
- `leibnizZeroFirstSmoothPieceIso` from `LeibnizZeroFirstPiece`. It is built from the
  published `generalLinearRestrictionDerivativeIso` and definitional equalities; see
  that module's Markdown;
- `mirabolicRankCastDerivativeIso` from `RankCastCompat` and
  `generalLinearRankCast_trans` from `Iteration`, which are equality eliminations of
  rank transports;
- the data `E` or `V`.

No Prop-valued statement definition is used as a hypothesis. The proofs use no
exactness, finite-length, admissibility or irreducibility theorem, and no conclusion
of an excluded consumer task. The constructions hold for arbitrary carriers in
universe `uV` and every unitary additive character `ψ`. They also hold at the top
order `d = n + 1` of the zero-first piece, where `MD n d` lands in `GL_0`.

## Related Library modules

`LeibnizZeroFirstPiece` (Worker 984) identifies `ρ × (σ|P)^(k)` with the zero-first
piece; this module adds the passage from the differentiated quotient term through
4.14(a). Worker 593's `LeibnizRestrictionCompat` compares the differentiated middle
and subobject terms of the restriction sequence with `leibnizSource` and the
right-mixed source. Worker 593's accepted, not yet published, `LeibnizRestrictionExact`
defines `leibnizRestrictionDerivativeQuotient T ψ m n d hd` as the same composite
`Q d`, so its objects and this module's agree definitionally. This module has no
declaration in common with those modules and imports neither.

## Declarations

All declarations are in namespace `Langlands.Derivative`. Throughout, `F` is a
`p`-adic field with topological data `T` and `ψ` is a unitary additive character.
`BNP a b` denotes the published `T.binaryNormalizedProductFunctor a b`, `LMP a r`
denotes `T.leftMixedProductFunctor a r` from `GL_a × P_(r+1)` to `P_(a+r+1)`, and
`MD N d hd` denotes `mirabolicDerivativeOfOrder T ψ N d hd` from `mirabolic N` to
`GL_(N+1-d)`. `Q d` is the composite displayed above.

- `leibnizRestrictionQuotientPieceIso T ψ m n d hd E`, for
  `hd : 0 < d ∧ d ≤ n + 1` and

  ```
  E : LMP (m+1) n ⋙ MD ((m+1)+n) d _ ⋙
        generalLinearRankCast T (_ : (m+1)+n+1-d = (m+1)+(n+1-d))
      ≅ 𝟭.prod (MD n d hd) ⋙ BNP (m+1) (n+1-d)
  ```

  is a natural isomorphism

  ```
  Q d ≅ leibnizPiece T ψ (m+1) (n+1) d (leibnizZeroFirstIndex m (n+1) d hd.2).
  ```

  The proof composes four isomorphisms, each whiskered by the identity on smooth
  representations of `GL_(m+1)` times the restriction `Res n` on the left:
  1. `mirabolicRankCastDerivativeIso` moves the mirabolic rank cast
     `(m+1)+n = m+n+1` of `restrictionQuotient` past `MD`, as a general-linear rank
     cast on the output;
  2. the composite of the two output rank casts is refactored, by
     `generalLinearRankCast_trans`, as the cast of `E` followed by the cast
     `leibnizZeroFirst_rank`;
  3. `E` replaces the derivative of the left mixed product by `A × B^(d)`;
  4. `leibnizZeroFirstSmoothPieceIso` identifies the result with the piece.
- `leibnizRestrictionQuotient_subsingleton T ψ m n d hd V X`, for
  `hd : 0 < d ∧ d ≤ (m+1)+(n+1)`, data

  ```
  V : ∀ A B, Subsingleton ((MD ((m+1)+n) d _).obj ((LMP (m+1) n).obj (A, B)))
  ```

  and a pair `X`, proves `Subsingleton ((Q d).obj X)`. The carrier of `(Q d).obj X`
  is that of `V` at `(X.1, Res n X.2)`, transported along two rank casts. The proof
  eliminates both equalities. It does not assume `n + 1 < d`. That assumption is only
  needed to obtain `V` from 4.14(a).

All declarations use universe levels `uF` (field) and `uV` (carriers of the factors),
as in the statement module. The checked axioms are `propext`, `Classical.choice` and
`Quot.sound`.
