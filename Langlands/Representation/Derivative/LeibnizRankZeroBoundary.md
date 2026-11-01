# Rank-zero boundaries of the Leibniz filtration

Author: Worker 984.

BZ77 Corollary 4.14(c) says that the `k`-th derivative of the product `ρ × σ` is glued
from the products `ρ^(j) × σ^(k-j)`. The published statement module
`Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement`
indexes the pieces by the finite set `leibnizIndices a b d` of pairs `(i, j)` with
`i ≤ a`, `j ≤ b`, `i + j = d`. Here `a` and `b` are the ranks of the two factors and
`d ≤ a + b` is the derivative order. Each index `x` has a piece functor
`leibnizPiece T ψ a b d x`, and the source functor is `leibnizSource T ψ a b d hd`.

This module treats the boundary where one factor has rank zero. There the index set
has exactly one element, and the module constructs a natural isomorphism from the
source functor to its unique piece. It does this for every derivative order `d`, both
for a rank-zero second factor (`b = 0`) and for a rank-zero first factor (`a = 0`).

The module adds no hypotheses and introduces no axioms. It states four index
lemmas, two reindexing lemmas and two `Nonempty` propositions, all proved. Every
other declaration is a definition: a representation equivalence or a natural
isomorphism. It does not prove the target statement
`GeneralLinearDerivativeLeibnizFiltrationStatement`. It supplies only the rank-zero
cases, which a single-piece gluing then closes.

## Provenance

This content is internal to the formalization (derived). BZ77
(`bernstein-zelevinsky-1977-induced-i`, content SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`), Corollary
4.14(c), printed p.458 (PDF p.19), states: "If `k ≥ 0`, then `(ρ × σ)^(k)` is glued from
`ρ^(j) × σ^(k-j)` (`j = 0, 1, ..., k`)". The source does not treat a rank-zero factor
separately. In that case only one index is feasible, and the assertion reduces to the
isomorphism built here. The proof here does not follow the source's route through
4.13. It reduces to the tensor model of the published normalized product with a
rank-zero factor, and uses the commutation of derivatives with an inert tensor factor
from `ZeroRankTensor`. That commutation matches BZ77 Proposition 1.9(g), printed
p.445 (PDF p.6). There the localization functors `r_(U,θ)`, from which the derivatives
are built, commute with `π ↦ π ⊗ τ`. The source states this without proof ("can be
directly verified"). This module only uses the Lean construction.

## Imports

- `Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement`
  (published): `leibnizIndices`, `LeibnizIndex`, `leibnizSource`, `leibnizPiece`.
- `Langlands.Representation.Derivative.RankCastCompat` (Worker 593, with Worker 984
  as coauthor): `generalLinearRankCastDerivativeIso`.
- `Langlands.Representation.Derivative.ZeroRankTensor` (Worker 969):
  `ZeroRankTensor.binaryRightZeroIso`, `ZeroRankTensor.generalLinearDerivativeTensorIso`.

The module uses these two modules without changing them. It also uses the published
`GeneralLinear.reindex`, the tensor models `BinaryTensor.rankZeroLeft`/`rankZeroRight`,
`BinaryTensor.compEquiv`, `binaryLeftZeroTensorEquiv`/`binaryRightZeroTensorEquiv`
with their naturality lemmas (`Langlands.Representation.Induction.BinaryProduct`), and
`generalLinearRankCast` with `generalLinearRankCast_trans` and
`generalLinearRankCast_symm_comp` (`Langlands.Representation.Derivative.Iteration`).

## Import closure and dependency audit

The direct imports are the statement module, `RankCastCompat`, `ZeroRankTensor`
and the shared `Langlands.Group.GL.ReindexCongr` helper.
At Library base `9a8ca758097242bde4147f33304f43fceef22fa4`, a recursive scan of the
`import Langlands.…` lines gives a transitive project closure of exactly these 77
modules, not counting this module. Integration adds only `ReindexCongr` to that
closure, for 78 dependencies; its sole dependency `GL.Basic` is already listed.
Each has a nonempty paired Markdown file:

- `Langlands.Group.GL`: `Basic`, `BlockModulus`, `Blocks`, `Mirabolic`, `MirabolicMixedProductSubgroups`, `MirabolicOppositeIntersection`, `MirabolicProjection`, `MirabolicRadical`, `Nonarchimedean`, `NonarchimedeanStatement`, `NormalizedCharacter`, `OppositeBlocks`, `Padic`, `PadicBlocks`, `RankMaps`, `RankReindex`, `UpperUnipotent`.
- `Langlands.HarmonicAnalysis`: `Basic`.
- `Langlands.LocalField`: `Canonical`, `Definitions`, `Normalization.Definitions`, `Normalization.Proof`, `Normalization.Statement`, `Topology`.
- `Langlands.Representation.Category`: `Basic`, `Subquotients`, `Twist`.
- `Langlands.Representation.Derivative`: `GeneralLinearDerivativeLeibnizFiltrationStatement`, `Homogeneity`, `Iteration`, `MirabolicCharacter`, `MirabolicMinus`, `RankCastCompat`, `ZeroRankTensor`.
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

No Lean file in this closure mentions segments, socles, classification, exhaustion,
supercuspidals or finiteness (case-insensitive text scan). In particular, the closure
does not contain `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`,
`IrreducibleCoinvariantFinitenessStatement`, `LeviCuspidalCoinvariantFinitenessStatement`,
or any module of the excluded segment, two-supercuspidal or classification tasks. The two
`Whittaker` modules only define additive characters, Whittaker functionals and function
models, with elementary lemmas about them.

The proofs use only the following inputs:
- the definitions `leibnizIndices`, `LeibnizIndex`, `leibnizSource` and
  `leibnizPiece`, and the lemma `mem_leibnizIndices`, from the statement module. The
  proposition `GeneralLinearDerivativeLeibnizFiltrationStatement` and the module's other
  proposition definitions are not used;
- the published constructions and naturality lemmas listed under Imports;
- the unchanged reflexive reindex theorem extracted into `ReindexCongr`;
- `generalLinearRankCastDerivativeIso` from `RankCastCompat`, which is equality
  elimination of a rank transport;
- `binaryRightZeroIso` and `generalLinearDerivativeTensorIso` from `ZeroRankTensor`,
  which are explicit isomorphisms built from coinvariant algebra on pure tensors.

No Prop-valued statement definition is used as a hypothesis. The proofs use no
exactness, finite-length, admissibility or irreducibility theorem, and no conclusion of
an excluded consumer task. The constructions hold for arbitrary carriers in universe
`uV`, arbitrary `GL_0` carriers and every continuous nontrivial additive character
`ψ`. They cover every order `d` up to the nonzero rank, including `d = 0` and the top
order, and the case where both ranks are zero.

## Related Library modules

This module neither imports nor duplicates the following related modules.
`GeneralLinearDerivativeLeibnizBoundary` (Worker 593) proves the order-zero (`d = 0`)
gluing for all ranks. The rank-zero boundaries here cover every order instead.
`LeibnizIndices` and `LeibnizPieceCompat` (Worker 593) handle index splitting and the
positive-order pieces. They have no declaration in common with this module. The
existing `Langlands.RankinSelberg.reindex_finCongr_self` is reused from
`Langlands.Group.GL.ReindexCongr`, which retains its original statement and proof
without importing downstream Rankin–Selberg constructions.

## Declarations

New declarations are in namespace `Langlands.Derivative`. Throughout, `F` is a `p`-adic field
with topological data `T`, `ψ` is a unitary additive character, `BNP a b` is the
published `T.binaryNormalizedProductFunctor a b`, and `GLD N d hd` is the published
`generalLinearDerivative T ψ N d hd` (from `GL_N` to `GL_(N-d)`).

### Index sets with a rank-zero factor

- `leibnizIndices_left_zero (hd : d ≤ 0 + b)`: `leibnizIndices 0 b d = {(0, d)}`.
- `leibnizIndices_right_zero (hd : d ≤ a + 0)`: `leibnizIndices a 0 d = {(d, 0)}`.
- `leibnizIndex_eq_left_zero (x : LeibnizIndex 0 b d)`: `x.val = (0, d)`.
- `leibnizIndex_eq_right_zero (x : LeibnizIndex a 0 d)`: `x.val = (d, 0)`.

All four are proved by `omega` from `mem_leibnizIndices`.

### Rank transport from carrier equivalences

- `reindex_finCongr_finCongr`: two entry-preserving reindexings
  `GeneralLinear.reindex (finCongr h)` and then `(finCongr h')` compose to the
  reindexing along `h.trans h'`, proved entrywise. The reused
  `Langlands.RankinSelberg.reindex_finCongr_self` identifies reindexing along
  a proof of `n = n` with the identity.
- `isoRankCastOfEquiv T h P Q e he`: for `h : m = n`, functors `P` into smooth
  representations of `GL_n` and `Q` into those of `GL_m`, and a family `e X` of
  representation equivalences from `P X` to `Q X` pulled back along
  `reindex (finCongr h.symm)` that is natural (`he`), the natural isomorphism
  `P ≅ Q ⋙ generalLinearRankCast T h`. After `subst h`, the reindexing is the identity
  and the rank transport is `𝟭`, so the components are the equivalences `e X`.

### Swapping a rank-zero factor

- `rankZeroRightSwapEquiv ρ`: for a representation `ρ` of `GL_n` on `V` and a vector
  space `W`, the tensor flip `V ⊗ W ≃ W ⊗ V` is an equivalence from the `b = 0` tensor
  model `rankZeroRight rfl ρ W` (rank `n + 0`) to the `a = 0` tensor model
  `rankZeroLeft rfl W ρ` (rank `0 + n`), pulled back along
  `reindex (finCongr (zero_add n).symm)`.
- `binaryNormalizedProductSwapZeroIso T n`:
  `Prod.swap ⋙ BNP n 0 ≅ BNP 0 n ⋙ generalLinearRankCast T (zero_add n)`.
  Its components are `binaryRightZeroTensorEquiv`, then the flip, then the inverse of
  `binaryLeftZeroTensorEquiv`. These are assembled by `isoRankCastOfEquiv`, and
  naturality follows from the two published naturality lemmas.
- `binaryNormalizedProductLeftZeroSwapIso T n`:
  `BNP 0 n ≅ Prod.swap ⋙ BNP n 0 ⋙ generalLinearRankCast T (zero_add n).symm`. This is
  the previous isomorphism whiskered by the inverse rank cast, using
  `generalLinearRankCast_symm_comp`.

### The two boundaries from a right-zero commutation

- `leibnizSourceRightZeroIso T ψ hd E x`: for `hd : d ≤ a + 0`, a natural isomorphism
  `E : BNP a 0 ⋙ GLD (a+0) d hd ≅ (GLD a d hd).prod 𝟭 ⋙ BNP (a-d) 0`, and the index
  `x : LeibnizIndex a 0 d`, the isomorphism
  `leibnizSource T ψ a 0 d hd ≅ leibnizPiece T ψ a 0 d x`. After identifying `x` with
  `(d, 0)`, the piece's derivative of the second factor is `GLD 0 0 = 𝟭`, its product
  is `BNP (a - d) (0 - 0) = BNP (a - d) 0`, and its rank cast is along
  `(a - d) + (0 - 0) = (a + 0) - d`, whose two sides are definitionally `a - d`, so the
  cast is `𝟭`. So the isomorphism is `E` followed by the forgetful functor to `Rep`.
- `leibnizSourceLeftZeroIso T ψ hd hb E x`: for `hd : d ≤ 0 + b`, `hb : d ≤ b`, the
  same `E` at rank `b`, and `x : LeibnizIndex 0 b d`, the isomorphism
  `leibnizSource T ψ 0 b d hd ≅ leibnizPiece T ψ 0 b d x`. After identifying `x` with
  `(0, d)`, it composes the following isomorphisms:
  1. `binaryNormalizedProductLeftZeroSwapIso` at `b`, moving the rank-zero factor to
     the right;
  2. `generalLinearRankCastDerivativeIso` (from `RankCastCompat`), commuting the rank
     cast along `b = 0 + b` with the order-`d` derivative;
  3. `E` at rank `b`;
  4. `binaryNormalizedProductSwapZeroIso` at `b - d`, swapping back;
  5. an `eqToIso` that merges the two remaining rank casts by
     `generalLinearRankCast_trans`.

### The right-zero commutation

- `binaryRightZeroDerivativeIso T ψ n d hd` (for `hd : d ≤ n + 0`):
  `BNP n 0 ⋙ GLD (n+0) d hd ≅ (GLD n d hd).prod 𝟭 ⋙ BNP (n-d) 0`. Write
  `TF = ZeroRankTensor.tensorFunctor` for `(X, A) ↦ X ⊗ A` with `GL_n` acting on `X`
  only, and `lift` for `MixedProductTensor.liftFunctor`. The isomorphism composes:
  1. `ZeroRankTensor.binaryRightZeroIso T n : BNP n 0 ≅ 𝟭.prod lift ⋙ TF`, whiskered
     by `GLD n d hd`;
  2. `ZeroRankTensor.generalLinearDerivativeTensorIso (GL_0) T ψ n d hd :
     TF ⋙ GLD n d hd ≅ (GLD n d hd).prod 𝟭 ⋙ TF`, whiskered by `𝟭.prod lift`. Its
     universe levels are given explicitly: inert factor `GL_0` in universe `uF`,
     carrier `max uV uF`. Then `𝟭.prod lift ⋙ (GLD n d hd).prod 𝟭` and
     `(GLD n d hd).prod 𝟭 ⋙ 𝟭.prod lift` agree definitionally;
  3. the inverse of `binaryRightZeroIso T (n - d)`, whiskered by `(GLD n d hd).prod 𝟭`.

### Final boundary isomorphisms

- `leibnizSourceRightZeroPieceIso T ψ hd x` (for `hd : d ≤ a + 0`,
  `x : LeibnizIndex a 0 d`): `leibnizSource T ψ a 0 d hd ≅ leibnizPiece T ψ a 0 d x`,
  which is `leibnizSourceRightZeroIso` with `E = binaryRightZeroDerivativeIso T ψ a d hd`.
- `leibnizSourceLeftZeroPieceIso T ψ hd x` (for `hd : d ≤ 0 + b`,
  `x : LeibnizIndex 0 b d`): `leibnizSource T ψ 0 b d hd ≅ leibnizPiece T ψ 0 b d x`,
  which is `leibnizSourceLeftZeroIso` with `E = binaryRightZeroDerivativeIso T ψ b d hb`
  and `hb : d ≤ b` from `hd`.
- `leibnizSource_iso_piece_of_right_zero` and `leibnizSource_iso_piece_of_left_zero`:
  the same isomorphisms, stated as `Nonempty (leibnizSource … ≅ leibnizPiece … x)`.

All declarations use universe levels `uF` (field) and `uV` (carriers of the factors),
as in the statement module. The checked axioms are `propext`, `Classical.choice`,
and `Quot.sound`.
