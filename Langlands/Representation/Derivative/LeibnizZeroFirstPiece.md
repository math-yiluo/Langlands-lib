# The zero-first Leibniz grade

Author: Worker 984.

BZ77 Corollary 4.14(c) says that the `k`-th derivative of the product `ρ × σ` is glued
from the products `ρ^(j) × σ^(k-j)`. The published statement module
`Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement`
indexes the pieces by the finite set `leibnizIndices a b d` of pairs `(i, j)` with
`i ≤ a`, `j ≤ b`, `i + j = d`, and gives each index `x` the piece functor
`leibnizPiece T ψ a b d x`.

This module treats one piece, the zero-first index `(0, d)`, for a first factor of
positive rank `m + 1`, a second factor of positive rank `n + 1` and a positive order
`d ≤ n + 1`. The published `LeibnizIndices` module names this index
`leibnizZeroFirstIndex m (n + 1) d`. The module constructs a natural isomorphism
between the following two functors on pairs `(A, B)`, with `A` on `GL_(m+1)` and `B`
on `GL_(n+1)`:

- restrict `B` to the mirabolic subgroup `P_(n+1) = mirabolic n`, take its order-`d`
  mirabolic derivative, form the binary product of `A` with it, transport the rank to
  `((m+1)+(n+1)) - d` and forget smoothness;
- the Leibniz piece at `(0, d)`.

This identifies the quotient term in the restriction filtration of `A × B` with a
Leibniz grade. The module adds no hypotheses and introduces no axioms. It states one
rank equation, proved by `omega`; the other two declarations are natural
isomorphisms. It does not prove the target statement
`GeneralLinearDerivativeLeibnizFiltrationStatement`.

## Provenance

This content is internal to the formalization (derived). BZ77
(`bernstein-zelevinsky-1977-induced-i`, content SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`), Proposition
4.13(a), printed p.458 (PDF p.19), gives the exact sequence
`0 → (ρ|P) × σ → (ρ × σ)|P → ρ × (σ|P) → 0`. Corollary 4.14(a), on the same page,
gives `(ρ × τ)^(i) = ρ × τ^(i)` for a mirabolic representation `τ` and `i ≥ 1`. The
source derives 4.14(c) from (a), (b) and 4.13(a). In that derivation the quotient term
`ρ × (σ|P)` contributes `ρ × (σ|P)^(k)`. By §4.3, printed p.454 (PDF p.15), the
general-linear derivative is `σ^(k) = (σ|P)^(k)` for `k ≥ 1` and `ρ^(0) = ρ`, so this
contribution is the piece `ρ^(0) × σ^(k)`.

This module proves only the last identification, for the actual Lean functors. It
does not use 4.13(a) or 4.14(a). Those are stated in the Library but not proved there,
and this module neither imports nor assumes them. The comparison is the published
`generalLinearRestrictionDerivativeIso` in the second factor. The order-zero
derivative of the first factor, the shape of the binary product and the rank cast all
agree definitionally.

## Imports

- `Langlands.Representation.Derivative.LeibnizPieceCompat` (published, Worker 593):
  `generalLinearRepRankCast` and `generalLinearRankCast_toRep`. Through it, the
  module uses the following published modules:
  - `LeibnizIndices` (Worker 593): `leibnizZeroFirstIndex`;
  - `RankCastCompat` (Worker 593, with Worker 984 as coauthor):
    `generalLinearRestrictionDerivativeIso`;
  - the statement module: `leibnizPiece`, `LeibnizIndex`;
  - `Iteration`: `generalLinearRestriction`, `generalLinearDerivative`,
    `generalLinearRankCast`;
  - `Homogeneity`: `mirabolicDerivativeOfOrder`;
  - `Induction.BinaryProduct`: `binaryNormalizedProductFunctor`.

The module does not change these modules.

## Import closure and dependency audit

The single direct import is `LeibnizPieceCompat`. At Library base
`3556873fa475ebf7c4932f5d037eb3dea71c4ddb`, a recursive scan of the
`import Langlands.…` lines gives exactly these 79 modules in the transitive project
closure, not counting this module. Each has a nonempty paired Markdown file:

- `Langlands.Group`: `GL.Basic`, `GL.BlockModulus`, `GL.Blocks`, `GL.Mirabolic`, `GL.MirabolicMixedProductSubgroups`, `GL.MirabolicOppositeIntersection`, `GL.MirabolicProjection`, `GL.MirabolicRadical`, `GL.Nonarchimedean`, `GL.NonarchimedeanStatement`, `GL.NormalizedCharacter`, `GL.OppositeBlocks`, `GL.Padic`, `GL.PadicBlocks`, `GL.RankMaps`, `GL.RankReindex`, `GL.UpperUnipotent`.
- `Langlands.HarmonicAnalysis`: `Basic`.
- `Langlands.LocalField`: `Canonical`, `Definitions`, `Normalization.Definitions`, `Normalization.Proof`, `Normalization.Statement`, `Topology`.
- `Langlands.Representation.Category`: `Basic`, `Subquotients`, `Twist`.
- `Langlands.Representation.Derivative`: `GeneralLinearDerivativeLeibnizFiltrationStatement`, `Homogeneity`, `Iteration`, `LeibnizIndices`, `LeibnizPieceCompat`, `MirabolicCharacter`, `MirabolicMinus`, `RankCastCompat`, `RightMixedProductDerivativeFiltrationStatement`.
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

A case-insensitive text scan finds no Lean file in this closure that mentions segments,
socles, classification, exhaustion, supercuspidals or finiteness. In particular, the
closure contains neither `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`,
`IrreducibleCoinvariantFinitenessStatement` nor `LeviCuspidalCoinvariantFinitenessStatement`.
It contains no module of the excluded segment, two-supercuspidal or classification tasks.
It also contains neither `MixedProductDerivativeStatement`, where 4.14(a) is stated,
nor any mirabolic-product restriction module of 4.13(a). The two `Whittaker` modules only
define additive characters, Whittaker functionals and function models, with elementary
lemmas about them.

The proofs use only the following inputs:

- the definitions `leibnizPiece` and `LeibnizIndex` from the statement module. The
  proposition `GeneralLinearDerivativeLeibnizFiltrationStatement` and the module's
  other proposition definitions are not used;
- `leibnizZeroFirstIndex` from `LeibnizIndices`, which is a definition;
- `generalLinearRestrictionDerivativeIso` from `RankCastCompat`. It is built from the
  rank-cast/restriction square `generalLinearRankCastRestrictionIso`, which is equality
  elimination, and from the defining equation `generalLinearDerivative_of_pos` of a
  positive-order derivative;
- `generalLinearRankCast_toRep` from `LeibnizPieceCompat`, which is equality
  elimination of a rank transport.

`RightMixedProductDerivativeFiltrationStatement` is in the closure because
`LeibnizIndices` uses its index set. This module does not use its proposition. No
Prop-valued statement definition is used as a hypothesis. The proofs use no
exactness, finite-length, admissibility or irreducibility theorem, and no conclusion of
an excluded consumer task. The constructions hold for arbitrary carriers in universe
`uV` and every continuous nontrivial additive character `ψ`. They also hold at the
top order `d = n + 1`, where the mirabolic derivative lands in `GL_0`.

## Related Library modules

`LeibnizPieceCompat` (Worker 593) gives the analogous identification
`leibnizPositivePieceIso` for the positive-first indices. Those indices come from the
right-mixed term `(ρ|P) × σ`. `LeibnizIndices` splits every Leibniz index into a
positive-first index or the zero-first index treated here. The order-zero case `d = 0`
is Worker 593's `GeneralLinearDerivativeLeibnizBoundary`. Worker 593's
`LeibnizRestrictionCompat` compares the differentiated middle and subobject terms of
the mirabolic restriction sequence with `leibnizSource` and the right-mixed source; this
module treats the quotient term instead. This module has no declaration in common with
those modules and does not import `LeibnizRestrictionCompat`.

## Declarations

All declarations are in namespace `Langlands.Derivative`. Throughout, `F` is a
`p`-adic field with topological data `T` and `ψ` is a unitary additive character.
`BNP a b` denotes the published `T.binaryNormalizedProductFunctor a b`, `Res n` denotes
`generalLinearRestriction T n` from `GL_(n+1)` to `mirabolic n`, `MD n d hd` denotes
`mirabolicDerivativeOfOrder T ψ n d hd` from `mirabolic n` to `GL_(n+1-d)`, and
`GLD N d hd` denotes `generalLinearDerivative T ψ N d hd`.

- `leibnizZeroFirst_rank (hd : d ≤ n + 1)`:
  `(m + 1) + (n + 1 - d) = ((m + 1) + (n + 1)) - d`, by `omega`.
- `leibnizZeroFirstSmoothPieceIso T ψ m n d hd`, for `hd : 0 < d ∧ d ≤ n + 1`:

  ```
  𝟭.prod (Res n) ⋙ 𝟭.prod (MD n d hd) ⋙ BNP (m+1) (n+1-d) ⋙
    generalLinearRankCast T (leibnizZeroFirst_rank hd.2) ⋙ SmoothRep.toRep
  ≅ leibnizPiece T ψ (m+1) (n+1) d (leibnizZeroFirstIndex m (n+1) d hd.2)
  ```

  The identity functor `𝟭` is on smooth representations of `GL_(m+1)`. The
  isomorphism is the product of the identity isomorphism with
  `generalLinearRestrictionDerivativeIso T ψ n d hd : Res n ⋙ MD n d hd ≅
  GLD (n+1) d hd.2`, whiskered on the right by the common tail. The rest holds
  definitionally. The composite `𝟭.prod (Res n) ⋙ 𝟭.prod (MD n d hd)` is the product
  `𝟭.prod (Res n ⋙ MD n d hd)`. The order-zero derivative `GLD (m+1) 0 _` in the piece
  is `𝟭`. The piece's product `BNP (m+1-0) (n+1-d)` is `BNP (m+1) (n+1-d)`. Rank casts
  along any two proofs of the same equation agree by proof irrelevance.
- `leibnizZeroFirstPieceIso T ψ m n d hd`: the same isomorphism with the tail
  `BNP (m+1) (n+1-d) ⋙ SmoothRep.toRep ⋙ generalLinearRepRankCast
  (leibnizZeroFirst_rank hd.2)`. The rank is transported in `Rep` after forgetting
  smoothness, as in `leibnizPositivePieceIso`. It is `leibnizZeroFirstSmoothPieceIso`
  preceded by the functor equality `generalLinearRankCast_toRep`.

Users with a composite total rank cast can first merge the casts with
`generalLinearRankCast_trans`.

All declarations use universe levels `uF` (field) and `uV` (carriers of the factors),
as in the statement module. The checked axioms are `propext`, `Classical.choice` and
`Quot.sound`.
