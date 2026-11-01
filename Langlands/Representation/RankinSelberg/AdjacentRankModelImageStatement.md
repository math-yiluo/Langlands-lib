# Large-second-twist image equality for the JPSS adjacent-rank model

Worker 1197 states
`Langlands.RankinSelberg.AdjacentRankModelImageStatement.{uF,uV}` in module
`Langlands.Representation.RankinSelberg.AdjacentRankModelImageStatement`.
This closed `Prop` definition is a source-derived interface for the image
assertion in JPSS Section 6.1, formula (8). It supplies no proof.

## Exact assertion

The proposition quantifies over every prime `p`, every
`F : PadicField.{uF} p` with its canonical topology, and every nontrivial
unitary additive character `ψ`. Nontriviality and continuity are fields
of `UnitaryAdditiveCharacter`. The scalar additive Haar measure `ν` and
the proof `hself : IsSelfDual ψ ν` remain supplied. It includes every
`r : ℕ`, including `r = 0`, and every complex module `V : Type uV`,
independently of the field universe.

The first block is an arbitrary representation `σ` of `GL_(r+1)(F)` on
its original `V`, with full standard Whittaker type
`IsOfWhittakerType r (standardCharacter ψ r) σ`. There is no
irreducibility hypothesis. For every specified
`ℓ : glFunctionals ψ r σ` with `ℓ.val ≠ 0` and every continuous
quasicharacter `χ₀`, the proposition says

```text
∃ C : ℝ, ∀ u : ℝ, C < u →
  ∃ J : glFunctionals ψ (r+1) ρᵤ, J.val ≠ 0 ∧
    range (Ψ ↦ (g ↦ Padic.adjacentRankModelIntegral F ψ ν hself σ ℓ χᵤ Ψ g))
      = range (v ↦ (g ↦ J.val (ρᵤ g v))).
```

Here the local names expand to existing published constructors:

```text
χᵤ = χ₀ * F.canonicalTopologicalData.unramifiedCharacterContinuous
  (LocalFactor.spectralParameter
    F.canonicalTopologicalData.residueCardinality
    F.canonicalTopologicalData.residueCardinality_real_pos (u : ℂ))

B = Shahidi.twoBlocks (r+1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)

ρᵤ = F.canonicalNormalizedOppositeParabolicInduced B
  (B.blockTensor (Shahidi.pairFamily σ
    (rankOneExtensionCharacter.{uF,uV} F χᵤ))).
```

The spectral parameter is `q^(-u)`, and the unramified character has value
`q^(-u ord(a))`. Consequently the pointwise complex value of `χᵤ(a)` is
`χ₀(a) * (normalizedAbs_F a : ℂ) ^ (u : ℂ)`. This is the prescribed
continuous character, with arbitrary fixed `χ₀`; its unitarity is not
assumed. The positive real twist affects only the second block.

The ordered lower shape is `(r+1,1)` inside the actual `GL_(r+2)(F)`.
Its inducing carrier family is
`Shahidi.pairCarrier V (ULift.{uV} ℂ)`. The second representation is
exactly the published lift of `rankOneCharacter` along
`ULift.moduleEquiv`, so its scalar action is multiplication by
`χᵤ(det a)`. The first representation remains `σ` on `V`.
The local instances explicitly select the canonical general-linear
topologies and their actual topological-group certificates in both ranks.
The induced representation is normalized opposite parabolic induction,
with its actual smooth section carrier and right-translation action.

The equality is between sets of scalar-valued functions on the whole
`GeneralLinear (r+2) F.Carrier`. Its left domain is the entire algebraic
`adjacentRankTestSpace ψ σ ℓ`, including all finite sums of pure tensors.
Its right domain is `ρᵤ.asModule`, the actual induced carrier.
Equality means that each tensor gives the coefficient of some vector of
this same `J`, and each induced vector has a tensor giving its coefficient,
in both cases at every `g`. The bound `C` precedes `u` and every tensor
or vector; `J` may depend on `u` but precedes both ranges. No
tensor-dependent bound or point-dependent functional is permitted.

The imported literal integral is used unchanged. In particular, its inner
measure is `generalLinearHaar F.Carrier r` on `GL_(r+1)(F)`, its absolute
value is the canonical normalized one, its kernel is
`[h, (ᵗh⁻¹) ε]`, and its scalar Fourier data remain the supplied `ψ`,
`ν`, and `hself`. No topology, norm, or completeness is supplied on `V`
or on the coefficient image. There are no added convergence, growth,
induced-type, transport, analytic-identity, or factor-existence premises.

## Source and derivation

The registered original is H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg Convolutions*, American Journal of
Mathematics 105 (1983), 367–464, source ID
`jpss-1983-rankin-selberg`. The retained Central-Library scan has SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 1197 visually read printed 376 and 427–431 (zero-based PDF
indices 10 and 61–65). The source-specific errata path
`notes/errata/jpss-1983-rankin-selberg.md` was absent from the declared
project, Library, and literature notes locations; no registered correction
was available there. This is a bounded registration check, not a claim
that no erratum exists.

Printed 427 introduces the fixed base character multiplied by `|·|^u`
and restricts the second character to large positive real `u`; it notes
that the fixed character may be taken unitary. The present interface
retains an arbitrary continuous base character. This is the usual
shift of the real parameter: a fixed quasicharacter on a nonarchimedean
local field is a real absolute-value power times a unitary character, so
its fixed real power is absorbed into the eventual bound.
That reduction is part of the later proof, not a hypothesis here.
The source's ambient rank `t` is `r+2`; its first block rank `t-1` is
`r+1`. The inverse transpose in formula (8) is defined in (0.3.6),
printed 376.

Printed 428 defines the partially Fourier-conjugated action `ρ₀` and
states the proposition for the tensor product of rectangular Schwartz
functions with the Whittaker model. Formula (8), printed 429, first
asserts convergence without a large-twist restriction and then asserts
the induced-model realization for sufficiently large `u`. These are
distinct claims. This proposition states only the latter image equality;
it does not assume or prove the separate convergence statement. The
published integral is a totalized scalar Bochner integral, so the
assertion can be formulated without any convergence premise.

For the second claim the source uses the open orbit through `[I,0]`.
On printed 430, (10) constructs sections from compactly supported
Schwartz functions on this orbit and first-block Whittaker vectors.
Formula (11) gives their actual normalized lower covariance: for a lower
block matrix with diagonal `(a,b)`, its scalar multiplier is
`σ₂(b) |b|^((t-1)/2) |det a|^(-1/2)`, and the first-block variable
changes by right translation by `a`. This is the lower normalized
induction used here, with the ordered pair of block sizes fixed.
It is not the upper shape `(1,r+1)` used by a separate adjacent-rank
consumer.

Still on printed 430, (12) applies a Jacquet integral to a section, and
substitution yields the double integral (13). Its absolute convergence
requires sufficiently large `u`; the source reduces this to a gauge
integral and leaves the final estimate as an exercise on printed 431.
Printed 431 then changes variables and integrates in the additive
variable first, obtaining (8) for a pure tensor. The conclusion uses
both that arbitrary test tensors are finite sums of pure tensors and
that the sections constructed by (10) span the induced representation.
These steps motivate both directions of the set equality and a single
functional on the induced representation. The analytic rearrangement,
uniform bound, functional construction, and spanning arguments remain
proof obligations.

## Original carrier and remaining obligations

On printed 427 the authors realize their representations by right
translation on their Whittaker models. Here the Schwartz tensor factor
uses the actual coefficient image `glCoefficientModel ψ r σ ℓ`, while
the induction uses the original representation `σ` on `V`. For a
reducible full Whittaker-type representation, the coefficient map
`V → functions` can have a kernel; this statement neither assumes nor
claims it is injective.

Consequently the interface is a source-derived assertion extending the
paper's chosen realization, not a verbatim theorem formulated in the
paper. A later proof owes actual transport between induction from the
coefficient model and this particular induction from `V`. In particular,
it must justify the induced coefficient image and the nonzero common
functional despite a possible coefficient-map kernel. No such induction
equivalence or coefficient-model transport is established by defining
this proposition, and none is inserted as a premise.

The module imports only the published integral model, lifted rank-one
character, two-block induction constructors, and opposite induction.
It changes no published pair. It proves neither the image equality nor
convergence, lower-to-upper reversal, star transforms, determinant-shell
expansions, or adjacent-rank gamma/L identities. It uses no unrestricted
multiplicativity or later adjacent-rank consequence. An independent
proof must target this exact proposition after its statement is public.
