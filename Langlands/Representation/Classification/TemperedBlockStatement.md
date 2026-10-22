# Tempered block induction and classification for GL_n

Authors: Worker 15; grouping interface coordinated with Worker 19.

This pair states normalized induction, exhaustion, unordered uniqueness and
equal-exponent grouping for tempered representations of GL_n. All declarations
are proposition definitions; none proves or assumes the asserted theorem.
The square-integrable blocks are specified by analytic conditions, without
assuming the special-segment classification as a constructor.

## Objects, universes and normalization

Fix a prime `p`, a finite p-adic extension `F : PadicField.{uF} p`, and a
compatible realization `T : F.TopologicalData`. Put `v = max uF uV`.
Every representation carrier lies in `Type v`. Normalized induction has carrier
universe `max uF v = v`, so exhaustion and grouping require no smaller-universe
representatives. No finite-dimensionality of representation carriers is assumed.
Ranks are positive: the rank-indexed clauses have `0 < n`; Whittaker clauses
use rank `n + 1`. `BlockShape n` specifies finitely many positive block ranks
summing to `n`, so its length cannot be zero when `n > 0`.

All representations are actual objects of `SmoothRep ℂ (GeneralLinear n
F.Carrier)`. Category isomorphisms are invertible equivariant linear maps.
Rank transport, written `h ▸ σ`, changes the group index along the displayed
natural-number equality and retains the representation. It is not equality
of informal labels or a chosen classification parameter.

`(T.normalizedProductInductionFunctor B).obj σ` is the published product
induction of the actual tensor product of the block representations, inflated
from the product Levi to the standard **upper** parabolic. Its covariance is
`f(pg) = δ_P(p)^(1/2) σ(p) f(g)` and its action is right translation.
`T.segmentFactor σ s` is the actual twist by `ν^s`, where `ν = |det|_F`
and `|ϖ|_F = q^(-1)`. These are Kudla §1.1's convention, printed pp.367–368,
including equation (1.1.3) and the accompanying right-translation convention.

`T.IsSquareIntegrable` requires admissibility, a unitary scalar central
character, and `L²` integrability of all descended absolute smooth matrix
coefficients on the actual central quotient. `T.IsTempered` uses
`L^(2+ε)` for every real `ε > 0` instead. Both quantify over all Borel Haar
measures of that quotient. The Library proves that such a measure exists.
Neither predicate is defined by induction, segments, or Jacquet exponents.

`IsUnitarizable` means existence of an `InvariantPositiveForm`: an actual
positive definite Hermitian form invariant under the representation. It is
stronger than merely asserting a unitary central character.
`Whittaker.IsGeneric ψ n` includes irreducibility and admissibility and asks
for an actual nonzero linear functional transforming under the standard
upper-unipotent character `u ↦ ψ(∑ᵢ uᵢ,ᵢ₊₁)`.
`UnitaryAdditiveCharacter` already requires continuity and nontriviality.
The genericity clauses apply to every such `ψ`, including rank one.

## Declarations and source correspondence

Names in the table belong to `Langlands.Classification`. The source key and
fingerprint list below identifies the exact retained editions.

| Declaration | Exact content | Source and derivation |
| --- | --- | --- |
| `SquareIntegrableBlockInduction F T` | Induction of any finite family of irreducible square-integrable unitarizable blocks is irreducible, unitarizable and analytically tempered. | Ja77 Corollary 3.3, p.99, for irreducibility; JS83 §1.2, p.109, states the smooth preunitary version. Ku94 §1.1, p.368, supplies preservation of unitarizability, and Proposition 2.2.1, p.373, supplies temperedness. |
| `SquareIntegrableBlockGenericity F T` | The same induced representation is generic for each `ψ`. | JS83 §1.2, pp.108–109, with the functional equation (1.2.3); Ku94 §2.3, p.374, confirms the functional definition and genericity of tempered representations. Ja77 Theorem 2.1(3), Lemma 3.1 and Corollary 3.3 support the unitary-mirabolic route, with the comparison obligations below. |
| `TemperedBlockExhaustion F T` | Each irreducible analytically tempered representation is isomorphic to such an actual product. | Ku94 Proposition 2.2.1, p.373, states precisely the tempered representations in this form. Ro82 §4.3, Proposition 12, p.212, states exhaustion; Proposition 11 identifies its square-integrable blocks. The invariant-form witnesses follow from Ca95 Proposition 2.5.4, p.29. |
| `TemperedBlockUniqueness F T` | Two products satisfying these block hypotheses are isomorphic iff their index sets are bijective with equal corresponding ranks and actual block isomorphisms after transport. | Derived from Ku94 Proposition 1.2.3, pp.369–370, Theorem 1.2.5(b),(d), pp.370–371, and the nonlinkage argument following Proposition 2.2.1, p.373. Ro82 Theorem 3(b) and Proposition 13, pp.211–212, provide the parallel quotient-classification and irreducibility statements. This is unordered discrete-series uniqueness, not a claim that arbitrary tempered inducing blocks have unique factorizations as tempered blocks. |
| `TemperedBlockInduction F T` | Products of irreducible tempered GL blocks are irreducible, unitarizable and tempered. | Ku94 §2.2, p.373, equation (2.2.2) and its following sentence: expand each tempered block into square-integrable blocks and use transitivity. Unitarizability follows from the square-integrable case. |
| `TemperedUnitarityAndGenericity F T` | Each irreducible tempered representation has an invariant positive form and is generic for every `ψ`. | Derived from exhaustion and the first two clauses. Ku94 §2.3, p.374, explicitly gives tempered genericity and independence of the character; JS83 §1.2, p.109, gives the preunitary tempered Whittaker description. |
| `SquareIntegrableEqualExponentGrouping F T` | A square-integrable Langlands datum admits the explicit grouping into a strictly decreasing tempered datum described below, with isomorphic induced standard modules. | Derived from Ku94 §2.2, p.373, equations (2.2.2)–(2.2.3) and the equal-exponent observation immediately before Theorem 2.2.2; normalization uses the analytic definition and invariant-form central-character argument below. |

`TemperedBlockTheorems F T` conjoins these seven clauses.
`PadicTemperedBlockTheorems` quantifies that conjunction over all primes,
all finite p-adic extensions and all compatible `T`, in the displayed
universes. The irreducibility assertions are specific to GL_n. No statement
here asserts irreducibility of tempered induction for general reductive groups.

## Meaning of the grouping clause

The input `d : T.SquareIntegrableLanglandsDatum n` contains actual irreducible
essentially square-integrable blocks, a unitary normalization exponent for
each, and weakly decreasing exponents. It contains no grouping or quotient
existence theorem. The clause first asserts that all normalized blocks
`ν^(-d.exponent i) d.blocks i` are analytically square-integrable.

It then asserts existence of `t : T.TemperedLanglandsDatum n` and a map `q`
from the old block indices to the new block indices, satisfying:

1. `q` is monotone and surjective; `d.exponent i = t.exponent (q i)`.
   Since the exponents of `t` are strictly decreasing, two old indices have
   the same exponent exactly when they have the same image under `q`.
   Monotonicity makes those fibers consecutive. Surjectivity rules out empty
   new blocks. Thus the fibers are the maximal equal-exponent runs.
2. For every new index `j`, there is a block shape `C` of `t.shape.size j`
   and a bijection `e` from its indices onto the fiber `{i // q i = j}`.
   The underlying old index of `e k` is strictly increasing in `k`.
   Equalities `C.size k = d.shape.size (e k).val` match the old ranks.
   The sum condition of `C` therefore says that the new rank is exactly
   the sum of the old ranks in the run; no block is omitted or duplicated.
3. There is an actual isomorphism from normalized induction along `C` of
   those old normalized factors, transported along the rank equalities,
   to `t.blocks j`. The latter is irreducible and analytically tempered by
   the fields of the existentially quantified `t`. These are conclusions
   of the statement, not hypotheses furnished by the input.
4. There is an actual isomorphism `d.induced ≅ t.standardModule`.
   The latter uses the strictly decreasing common run exponents. This is
   the interface needed to transfer a regular-chamber quotient theorem.
   The assertion introduces no canonical quotient and states no such theorem.

For the initial normalization assertion, essential square-integrability gives
an exponent `s` whose normalized representation is square-integrable and has
unitary scalar central character. The chosen exponent `a` of `d` gives an
invariant positive form on `ν^(-a)π`; that form forces its scalar central
action to be unitary. Comparing central actions at `ϖ I_r` gives
`|ϖ|^(r*(s-a)) = 1`. Since `r > 0`, this forces `s = a`.
The grouping then applies square-integrable induction within each run,
commutes the common determinant twist with induction, and uses transitivity.
These are mathematical explanations of the derived statement; their proofs
are not implemented here.

## Source boundaries and remaining proof obligations

Ja77 §0, p.91, works throughout with unitary Hilbert representations and
Mackey induction. Its genericity is the mirabolic isotypic condition.
Lemma 3.1, pp.96–97, obtains a nonzero Whittaker functional on smooth vectors
and uses multiplicity one. Theorem 3.2 and Corollary 3.3, pp.98–99, establish
irreducibility and genericity for unitary generic, respectively square-integrable,
factors. The chosen parabolic on p.98 is the transpose of a standard parabolic.
Using this route requires identifying smooth normalized induction with smooth
vectors in unitary induction and comparing opposite parabolics by conjugation
and block reversal. These comparisons are not assumed by this statement.
JS83 pp.108–109 gives the smooth formulation with upper parabolics and the
actual Whittaker functional and is the direct source for that formulation.

Ja77 contains no assertion or proof of tempered exhaustion or its unordered
uniqueness. Ro82 Proposition 12 and Ku94 Proposition 2.2.1 both cite Jacquet,
but their citation does not fill that gap. Here Ro82 and Ku94 are the explicit
sources for the exhaustion statement. A sufficient proof source for general
tempered support/exhaustion, and its comparison with the analytic predicate,
remains to be obtained and audited before a proof is claimed. The uniqueness
statement has the separate multisegment-classification route specified in the
table; it is not attributed to Ja77. Bernstein's square-integrable converse
and the multisegment classification remain proof dependencies. The Library's
`SegmentSquareIntegrabilityStatement` and its paired source audit retain the
omitted-proof and later-duality-source boundaries for the converse.

Further Lean proof obligations include construction of invariant forms under
normalized induction; square-integrable admissibility and unitarity; tempered
preservation and exhaustion; the block permutation and uniqueness isomorphisms;
actual Whittaker functionals and character independence; twist/induction
compatibility and induction transitivity; and the finite ordered grouping
construction with its rank transports. The published special-block statements
and the segment-product genericity installment are not assumptions of these
propositions and are not duplicated here.

The analytic Library predicates use all Borel Haar measures rather than a
single Haar measure. Comparison with the sources uses uniqueness of Haar
measure up to positive scalar and invariance of `L^p` membership under that
scaling. Admissible smooth matrix coefficients agree with the smooth-dual
coefficients used here. Comparison with a Schwartz-space or exponent-based
notion of temperedness is a separate theorem, not a definition. These
comparison proofs remain obligations. The ordinary unitary central-character
condition alone is never substituted for existence of an invariant positive form.

## Published dependencies and retained source editions

This pair was developed against Library commit
`e7e1cf75d8341a5fe60f25d4e6bb64d251921cbf`. Its direct imports are
`Langlands.Representation.Classification.LanglandsData` and
`Langlands.Representation.Whittaker.GeneralLinear`. The actual imported
interfaces are:

| Published module | Used declarations |
| --- | --- |
| `Classification.LanglandsData` | `SquareIntegrableLanglandsDatum`, its `exponent` and `induced`; `TemperedLanglandsDatum` and its `standardModule` |
| `Classification.Tempered` | `T.IsSquareIntegrable`, `T.IsTempered`, `T.IsEssentiallySquareIntegrable` |
| `Classification.Segments` | `T.segmentFactor`, an actual determinant twist |
| `Induction.BlockFactors` | `T.normalizedProductInductionFunctor` |
| `Unitary.Basic` | `IsUnitarizable`, `InvariantPositiveForm` |
| `Whittaker.GeneralLinear` | `Whittaker.IsGeneric` and the standard upper-unipotent character |
| `HarmonicAnalysis.Basic` | `UnitaryAdditiveCharacter` |

These are current published mathematical definitions at that commit; no draft
module is imported. The source-derived clauses have no theorem-valued input
standing in for classification. The later proof may use the separately published
`SegmentEssentialSquareIntegrableClassification`,
`SegmentSpecialParameterUniqueness`, and
`EssentialSquareIntegrabilityExponentUniqueness` statements as proof targets,
and the induction-transitivity statement family; their truth is not assumed here.

All five sources below were already registered and were read directly in their
retained editions. No source-specific errata note for them was present in the
current Library. Page numbers are printed page numbers; parenthetical PDF
numbers are one-based.

- **Ja77**: H. Jacquet, *Generic representations*, LNM 587 (1977), pp.91–101
  (PDF pp.97–107 of the retained volume), read in full.
  ID `provided-7fa6dd7a9bc39b0ef92f41d27dd4970725cdfbe795124370c63ffe3d8743b116`;
  SHA-256 `073cdfbdac1db264653544249d1060ba47704cc1678a5f545b9cd0ca5df46c8a`.
- **JS83**: H. Jacquet and J. A. Shalika, *The Whittaker models of induced
  representations*, Pacific J. Math. 109 (1983), pp.107–120; read §§1.1–1.3
  and the beginning of §2, pp.107–110 (PDF pp.2–5).
  ID `jacquet-shalika-1983-whittaker`;
  SHA-256 `e171831da6c064fdcb55efe79381ba1f85daa4efd7f3a79071589ffee9527f98`.
- **Ro82**: F. Rodier, *Représentations de GL(n,k) où k est un corps p-adique*,
  Astérisque 92–93 (1982), pp.201–218; read §4.3, Theorem 3 and
  Propositions 11–13, pp.211–212 (PDF pp.12–13), and surrounding pp.213–214.
  ID `rodier-1982-gln`;
  SHA-256 `389a9155f59022f5f5403bf568216f66b407b6d47e98221d115dcd85e076c8fc`.
- **Ku94**: S. S. Kudla, *The local Langlands correspondence: the
  non-archimedean case*, Motives, Part 2, PSPM 55 (1994), pp.365–391;
  read pp.367–374 (PDF pp.377–384 of the retained whole volume), especially
  §1.1, Theorem 1.2.5(b),(d), Proposition 2.2.1, equations (2.2.2)–(2.2.3),
  and §2.3. Proposition 2.2.1 is on printed p.373, after the definition on p.372.
  ID `kudla-1994-local-langlands-nonarchimedean`;
  SHA-256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
- **Ca95**: W. Casselman, *Introduction to the theory of admissible
  representations of p-adic reductive groups*, draft of 1 May 1995;
  read §2.5 and Proposition 2.5.4, pp.28–29 (PDF pp.28–29).
  ID `casselman-1995-admissible-representations`;
  SHA-256 `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
