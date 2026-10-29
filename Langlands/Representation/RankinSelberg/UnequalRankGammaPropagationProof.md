# Same-multiplier propagation of the unequal-rank gamma equation

Worker 396 authored the induction and final assembly. The supplied-data
telescope follows Worker 331's published propagation statement and Worker
11's earlier functional-equation statement. The valuative-topology bridge
reuses `Langlands.HarmonicAnalysis.rowFourierCutoff_nonarchimedean`.
The substantive transfer and adjacent-span results are imported from their
published proof modules.

`Langlands.RankinSelberg.unequalRankGammaPropagation.{uF,uV,uW}` proves
exactly [UnequalRankGammaPropagationStatement](UnequalRankGammaPropagationStatement.md).
Its binders are implicit `{p : ℕ}` and `[Fact p.Prime]`, then explicit
`F : PadicField.{uF} p`, `T : F.TopologicalData`, and `n r : ℕ`.
The field and two representation universes remain independent.

For every supplied rational function `G`, the literal block-zero equation
implies `UnequalRankGammaEquation` with the same `G`. The original supplied
character, topology, compatible quotient measure `μ`, self-dual scalar Haar
measure `ν`, representations and nonzero Whittaker functionals occur at every
block. The proof retains the complete Whittaker-type scope. It introduces no
irreducibility, analytic-existence, common-generator, gamma-existence or
epsilon-existence hypothesis. The target pair and its import closure are
unchanged.

## Published transfer and adjacent-span inputs

[unequalRankComplementaryTransfer](UnequalRankComplementaryTransferProof.md)
constructs, for every pair `f,f′` at `(j+1,k)`, one coefficient `f₀` in the
original model, chosen before two real bounds `a,b`. For that same `f₀,f′`,
the actual original integrals agree with those at `(j,k+1)` when `a < Re(s)`,
and the actual complementary-dual integrals agree when `b < Re(s)`.
The dual integral is literally `dualUnequalRankModelIntegralAt`: its inverse
character, inverse-transpose transforms, right translation by `blockWeylAt`,
and complementary rectangular measure are retained.

This published dependency implements the root/Fourier construction. Uniform
compact support and smoothness choose a normalized even Fourier pair. The
shared actual-representation smearing theorem constructs one averaged
coefficient whose original and transformed formulas give both required
identities. Genuine integrability justifies each last-row rectangular Fubini
step. Equality of the resulting inner integrals then gives equality of the
outer integrands; no quotient integral is interchanged with a rectangular
integral. All row and rectangular measures are products of the supplied `ν`.
The normalized cutoff has mass one for that same measure, so no scalar factor
is introduced in either continuation. These facts are provided by the imported
proof, rather than new assumptions of the propagation theorem.

[unequalRankAdjacentBlockSpan](UnequalRankBlockSpanProof.md) gives equality
of the Laurent spans of the actual original rational-value sets at `(j+1,k)`
and `(j,k+1)`. Its forward transfer integrates a last row in the original
coefficient model. Its reverse transfer uses a normalized small cutoff and
the same published Fourier-smearing construction. Its arbitrary-Haar Fourier
surjectivity dependency explicitly transports any reference normalization by
the nonzero Haar ratio; the final equality uses precisely the supplied `ν`.
No functional equation or common generator is an input to either dependency.

## Transporting the identical continuation and a nonzero value

The proof reuses
`RationalContinuationLinear.continuation_of_eq_on_right`, packaging the
supplied half-plane bound into its existential argument. Suppose actual
spectral functions `f,g` agree on `a < Re(s)` and `g` has
rational continuation `R` beyond `b`. The maximum of `a,b` is a valid
continuation bound for `f` with exactly the same `R`. The proof copies the
canonical-denominator nonvanishing condition from the old continuation and
composes the two equalities. It performs no rational simplification and needs
no uniqueness or cancellation result.

`propagation_nonzero_of_zetaSpan_eq` is another internal consequence of the
published Laurent-span definition. If every member of the new value set were
zero, its span would be bottom. Span equality would put the old nonzero value
in bottom, contradicting its nonvanishing. Thus adjacent-span equality
transports existence of a nonzero actual rational value, without identifying
a normalized generator or asserting that every coefficient has a nonzero
continuation.

## Induction retaining the supplied multiplier

`unequalRankGammaEquation_of_pairedTransfer` works with fixed coefficient
models and actual integrals. Its explicit adjacent-span and paired-transfer
premises isolate the induction; the final theorem discharges both with the
published unconditional proofs.

The block-zero antecedent supplies one `ζ`, its model minus-one scalar
property, a nonzero original rational value, and the continuation/equation
clauses for every `f,f′`. The proof chooses this same `ζ` for the full
conclusion, before quantifying over the blocks.

It inducts on `j`, with `k` and the rank equality quantified in each step.
For `j=0`, the equality `r = n + (0+k+1)` identifies `k = r-n-1`.
The supplied block-zero clauses therefore give the base case directly.
For the successor block `(j+1,k)`, the induction hypothesis applies at
`(j,k+1)`. Span equality transports its nonzero-value clause. For each
`f,f′`, paired transfer chooses one `f₀`. Apply the preceding block's equation
to `f₀,f′`, obtaining `R,Rdual`, their two actual continuations, and the gamma
equation. The two half-plane equalities transport precisely these rational
functions to the new block.

The final step reuses the old `GammaFunctionalEquation` proof verbatim.
Thus `ζ`, `G`, `R`, `Rdual`, the exponent `r` for the larger group of rank
`r+1`, and the reflected argument `1-s` are identical. The existing three
canonical-denominator conditions, for `G` and the two continuations, are
preserved without cancellation. No nonvanishing of `G` is required.

The final p-adic assembly installs the structures belonging to the supplied
`T` and the target's Borel structures. The imported
`rowFourierCutoff_nonarchimedean` uses the valuation topology's basis of open
additive submodules and adds no hypothesis. It applies the two published theorems at that same `F,T,n,r` and
all the supplied measures, representations and functionals. The inline
block-zero antecedent is definitionally the existing
`UnequalRankBlockZeroGammaEquation`; it is neither changed nor strengthened.
The induction also covers `n=0`, zero-dimensional rectangular blocks, and the
adjacent-rank case whose only block is `(0,0)`.

## Original sources and internal provenance

The source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`.
Theorem 2.7, printed pp.390–391, gives the Whittaker-type scope and the
complementary-block functional equation. The Fourier lemma is on pp.394–395.
Section 2.8, p.395, reduces to block zero and preserves the proportionality
constant in passage between blocks. The source ranks are Lean `r+1,n+1`,
so its sign exponent for the larger group is Lean `r`.

That passage explicitly refers to Theorem 4.5 of *Automorphic Forms on GL(3) I*
(1979), registered as `jps-1979-gl3-i`, whose induction on printed pp.197–198
uses a lower-row average, complementary Fourier cutoff, support and smoothness.
The relevant original pages and formula images were read during development;
no source-specific erratum was found in the available project and Library
errata notes. The retained source paths and SHA256 fingerprints are recorded
in the unchanged target's Markdown.

The paired transfer implements those operations using the shared published
smearing, compact-support, finite-Schwartz-expansion, conjugation and
rectangular-integration results. This module adds the formal induction and
the nonzero-value transport, reusing the existing continuation transport. The rational
predicate packaging, span argument and maximum-bound argument are internal
derived formulations, not assertions that the originals use those interfaces.
Worker 623 authored the imported paired-transfer assembly; Worker 180 authored
the imported adjacent-span proof. Their published declarations are reused by
Lean name, without copying their implementations or relying on a shared draft.
