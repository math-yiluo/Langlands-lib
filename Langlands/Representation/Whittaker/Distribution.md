# Whittaker bi-equivariant distributions and Weyl-conjugated transpose

This module constructs the distribution interface on the actual group
`GeneralLinear (n + 1) R`, for a commutative topological ring `R` in arbitrary
universe `uR`. Rank one is included by `n = 0`. It reuses the existing
`HarmonicAnalysis.Distribution` (the algebraic complex dual of the actual
`SchwartzBruhat` space), test-function transports, upper-unipotent subgroup,
standard character, long-Weyl matrix and transpose homeomorphism.

## Involution and character

`weylTransposeHomeomorph n R` composes `Distribution.transposeHomeomorph`
with conjugation by `GeneralLinear.weylLong (n + 1) R`. Thus, writing `w` for
the actual matrix with anti-diagonal entries one,

\[
\tau(g)=w g^t w,\qquad \tau(g)_{ij}=g_{\operatorname{rev}(j),\operatorname{rev}(i)}.
\]

The entry formula follows from the published Weyl multiplication and
transpose formulas. Reversing indices twice proves involutivity; the
transpose multiplication law and `w*w = 1` prove
`tau(g*h) = tau(h)*tau(g)`. In rank one, all indices agree and tau is the
identity. Reversal reverses strict inequalities, so the entry formula
preserves upper triangularity and diagonal entries one. The restriction
`weylTransposeUnipotent` is a homeomorphism of the actual subgroup and is
involutive.

The first-superdiagonal entry indexed by `i : Fin n` becomes the entry
indexed by `i.rev`; `Fin.rev_succ` and `Fin.rev_castSucc` establish this
identity. Reindexing the finite sum by `Fin.revPerm` proves preservation of
the superdiagonal sum, including the empty sum in rank one. Applying the
existing additive character proves `standardCharacter_weylTranspose` as an
equality in complex units. No nontriviality assumption on the additive
character is needed for these elementary identities.

## Distribution conventions

For `chi = standardCharacter psi n`, the proposition
`IsBiEquivariantDistribution` means exactly

\[
D\bigl(L_{u_1^{-1}}R_{u_2}f\bigr)
 =\chi(u_1)\chi(u_2)D(f),\qquad u_1,u_2\in U.
\]

Here the existing translations are `L_a f(g) = f(a⁻¹*g)` and
`R_b f(g) = f(g*b)`. Consequently the translated test function is exactly
`g ↦ f(u₁*g*u₂)`. Both character factors have positive exponent; neither an
inverse character nor a complex conjugate occurs. `biTranslate_apply` and
`biTranslate_eq_pullback` prove this evaluation and identify it with
pullback by the composite of the existing left and right homeomorphisms.
`isBiEquivariantDistribution_iff` gives the same equation using that pullback.

`IsWeylTransposeInvariant n R D` is the proposition `tau_*D = D`, using the
existing distribution pushforward. Its evaluation equivalence is
`D(pullback tau f) = D(f)` for every test function, or `D(f ∘ tau) = D(f)`.
Evaluation of equality proves one direction; linear-map extensionality
proves the converse. Pushforward is involutive by the existing composition
law and the pointwise involutivity of tau. There is no Haar or modular factor.

The definitions and elementary laws require only `CommRing R`,
`TopologicalSpace R`, and `IsTopologicalRing R`; no field, Hausdorff, local
compactness or total-disconnectedness hypothesis is used. A checked example
specializes to every `PadicField.{uF}` with `F.canonicalNormedField`, with
`uF` unrestricted and independent of the complex scalar universe.

## Original source and scope

J. A. Shalika, *The multiplicity one theorem for GLn*, Annals of Mathematics
(2) **100** (1974), 171–193, registered source
`shalika-1974-multiplicity-one`, printed pp.173–175 (PDF pages 4–6), supplies
the source conventions. The original PDF is
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`,
SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Worker 88 independently read these pages and visually checked pp.174–175;
no source errata file was found in project or Library notes.

On p.174, taking every first-superdiagonal coefficient equal to one permits
`h₀ = 1` in Shalika's anti-automorphism, giving the tau above. The elementary
subgroup and character preservation laws match (1.3)–(1.4). The translations
are defined on p.174. Proposition 1.8 on p.175 explicitly writes the
test-function equation with `L_(u₁⁻¹) R_u₂` and `chi(u₁u₂)`, resolving the
sign convention independently of notation for dual actions. Its character
factor equals our product because `standardCharacter` is a homomorphism.
The proposition there concerns distributions on a Bruhat cell; this module
uses its equation as the global equivariance predicate for the distribution
problem of Theorem 1.6.

The general-ring elementary identities and evaluation equivalences are
internal consequences of the reused definitions, with the implemented
proofs described above. They extend the source's local-field setting only
at this elementary level. This module neither states nor proves that every
bi-equivariant distribution is tau-invariant. Shalika's Theorem 1.6, a
multiplicity bound, genericity, and a bridge to smooth duals remain separate
obligations. No representation or unitarity hypothesis is introduced here.
