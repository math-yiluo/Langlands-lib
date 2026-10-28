# Stabilized lower Jacquet data for the strict rank-one extension

This module defines the scalar integrand, the compact-open stable graph, the domain of
sections where that integrand stabilizes, the stable linear value on that domain and a
conditional extension to all sections. It is the stabilized lower Jacquet
construction used in the early argument of JPSS Lemma (5.5). It proves only
elementary facts about these definitions: linearity, uniqueness of the stable value
and compatibility with right translation. It does **not** prove that any particular
section stabilizes, that the global stable domain is the whole section space, that
the resulting functional is nonzero or is a Whittaker functional, or any zeta or
integral comparison.

## Source and provenance

The original source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions*, Amer. J. Math. 105 (1983), registered as `jpss-1983-rankin-selberg`
(file SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`).
The relevant places are Section 3.1, printed pages 404–405 (PDF pages 39–40), and the
proof of Lemma (5.5), printed page 424 (PDF page 59). No errata for this source were
available in the project literature directory when these definitions were prepared.

On printed page 424 the proof of Lemma (5.5) defines the functional on the lower
induced representation in formula (1) as a **limit**, over an increasing exhausting
sequence of compact open subgroups `V^ν` of the unipotent variable, of the truncated
integrals of the scalar contraction `μ(f(v))` against the conjugate character
`θ̄(v)`. The source refers to (4.5) for the existence of this limit. Formula (3)
there is a formal ordinary integral `W_f(g) = ∫ f(vg; e) θ̄(v) dv`, and the later
Fubini and dominated-convergence argument applies only to chosen sections and test
coefficients.

This module follows formula (1), not formula (3). The graph uses the published
compact-open stable integral `Langlands.HarmonicAnalysis.HasStableIntegral`: the
integrand must be genuinely integrable on every compact open additive subgroup
containing one fixed compact open subgroup, with a common value. This graph and
domain interface is an internal formulation of compact-open stabilization derived
from formula (1). It is not stated in this form in the source. It does not assert
ordinary absolute convergence, and no ordinary Bochner integral of a possibly
non-integrable function stands for the stable value. The Lean does not prove any
comparison between this notion and the limit along one particular sequence
`V^ν`. The source's assertion that the limit exists for every section is not
formalized here. The conditional extension below takes it as an explicit
hypothesis.

The declaration names, the transport through `asModuleEquiv` and the packaging as
submodules and linear maps are implementation choices.

## Parameters and conventions

The parameters are a prime `p` and `F : PadicField.{uF} p` with its canonical
topology. We also take any natural `t`, an arbitrary quasicharacter `χ`, and any
complex module `W` in the independent universe `uW`. We take any representation `σ`
of `GL_(t+1)(F)` on `W`, a supplied unitary additive character `ψ`, and a supplied
inverse-character functional `ℓ` in `Whittaker.glInverseFunctionals ψ t σ`. No
smoothness, irreducibility, genericity or nonvanishing hypothesis is imposed.

Sections are the actual carrier `rankOneExtensionLowerSection F t χ σ` of the
published lower induction `rankOneExtensionLowerModel F t χ σ`. That induction has
total rank `1 + (t + 1)`, reversed inducing order `(σ, χLift)` and scalar carrier
`ULift.{uW} ℂ`. All of this comes from
`Langlands.Representation.RankinSelberg.RankOneExtensionAnalyticData`.

The row variable is `y : Fin (t + 1) → F.Carrier`, with the product of the canonical
topology and the product (`MeasurableSpace.pi`) of the Borel measurable space. The
measure is the published `HarmonicAnalysis.rowMeasure ν.val (t + 1)`, the finite
product of a supplied self-dual Haar measure
`ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`. No
measure is chosen and no new normalization is introduced.

## Declarations

### Compact open witness

`rankOneExtensionRow_exists_compactOpen F t` proves that the row space has a compact
open additive subgroup, namely the integral rows `𝒪^(t+1)`. The proof uses the
canonical data's `isOpen_integers` and `isCompact_integers`. This is the witness the
generic `stableIntegrableSubmodule` and `stableIntegral` require. It is derived from
the canonical `p`-adic data and is not an extra premise.

### Right translation of sections

`rankOneExtensionLowerTranslate F t χ σ h` is the actual induced right action
`rankOneExtensionLowerModel F t χ σ h`, written as a complex-linear endomorphism of
the section carrier by conjugating with `asModuleEquiv`. The theorem
`rankOneExtensionLowerTranslate_asModuleEquiv` records this. The theorem
`rankOneExtensionLowerSectionEval_translate` says the translate by `h` evaluates at
`g` as `f` evaluates at `g * h`.

### Item 1: the scalar integrand

`rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g` is the function

`y ↦ rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f (rankOneExtensionUpperCell t y * g) * ψ.complex (y (Fin.last t))`.

In words, it is the published scalar contraction of the section, evaluated at
`u(y) g` with `u(y) = [I, y; 0, 1]`, times the **positive** character of the last row
coordinate. The lemma `rankOneExtensionStableIntegrand_apply` states this formula.
The contraction is the published one, defined from `ℓ` and section evaluation. No
new function model and no topology on `W` is used.

The factor is positive because `ℓ` is an *inverse*-character functional. The task
contract prescribes this sign for the inverse-functional conventions, in place of
the source's conjugate factor `θ̄`. This module proves no Whittaker transformation
law for the integrand or the resulting functional.

`rankOneExtensionStableIntegrandMap F t χ σ ψ ℓ g` is the same integrand as a
`ℂ`-linear map from sections to functions on rows. Linearity holds because section
evaluation and the tensor contraction are linear.
`rankOneExtensionStableIntegrand_translate` states that translating `f` by `h`
replaces `g` by `g * h`.

### Item 2: the stable graph

`HasRankOneExtensionStableJacquetAt F t χ σ ψ ℓ ν f g z` is defined as exactly

`HasStableIntegral (rowMeasure ν.val (t + 1)) (rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g) z`.

It is a proposition (`Prop`).

- `HasRankOneExtensionStableJacquetAt.unique` proves that two stable values at the
  same `(f, g)` are equal. It applies `HasStableIntegral.unique` directly.
- `hasRankOneExtensionStableJacquetAt_translate_iff` says the graph at the translate
  `(h · f, g)` is equivalent to the graph at `(f, g * h)`.

### Item 3: the stable domains

- `rankOneExtensionStableDomainAt F t χ σ ψ ℓ ν g` is the comap of the published
  `stableIntegrableSubmodule` under the integrand map at `g`. By
  `mem_rankOneExtensionStableDomainAt`, membership means exactly
  `∃ z, HasRankOneExtensionStableJacquetAt … f g z`.
- `rankOneExtensionStableDomain F t χ σ ψ ℓ ν` is the infimum over all `g` of these
  submodules. By `mem_rankOneExtensionStableDomain`, membership means exactly
  `∀ g, ∃ z, HasRankOneExtensionStableJacquetAt … f g z`.
- `rankOneExtensionStableDomain_eq_top_iff` says this domain is `⊤` exactly when every
  section stabilizes at every `g`. This is only a reformulation. Nothing here asserts
  that the domain is `⊤`.
- `rankOneExtensionStableDomain_le_at` gives the inclusion into each `DomainAt`.
- `rankOneExtensionLowerTranslate_mem_stableDomain` proves that the global domain is
  invariant under the actual induced right action. The proof uses the translation
  identity.
- `rankOneExtensionStableDomainTranslate` is the restriction of the right action to
  the global domain. Its value is computed by
  `rankOneExtensionStableDomainTranslate_val`.

### Item 4: the stable value and the stable functional

`rankOneExtensionStableValueAt F t χ σ ψ ℓ ν g` is a linear map from the global
stable domain to `ℂ`. It composes the published `stableIntegral` with the integrand
map at `g`, codomain-restricted to `stableIntegrableSubmodule`. That restriction is
possible because of the inclusion into `DomainAt g`. So the value comes from proved
stabilization, and no default value is assigned to any divergent integrand.

`rankOneExtensionStableFunctional F t χ σ ψ ℓ ν` is the stable value at the identity.
The following facts are proved:

- `hasRankOneExtensionStableJacquetAt_stableValueAt` and
  `hasRankOneExtensionStableJacquetAt_stableFunctional` give the defining graph.
- `rankOneExtensionStableValueAt_eq_iff` and `rankOneExtensionStableFunctional_eq_iff`
  characterize the value uniquely as the stable value.
- `rankOneExtensionStableValueAt_translate` states right translation: the value at `g`
  of the translate by `h` equals the value of `f` at `g * h`.
- `rankOneExtensionStableFunctional_translate` states evaluation: the stable
  functional of the translate by `g` equals the stable value at `g`.

### Item 5: conditional extension

`rankOneExtensionStableExtension F t χ σ ψ ℓ ν hall` takes an explicit proof `hall`
that the global stable domain equals `⊤`, and gives the stable functional on the
whole actual section carrier.

- `rankOneExtensionStableExtension_apply` unfolds it.
- `hasRankOneExtensionStableJacquetAt_stableExtension` and
  `rankOneExtensionStableExtension_eq_iff` give its stable graph at the identity.
- `hasRankOneExtensionStableJacquetAt_stableExtension_translate` gives the
  right-translation formula: the extension at the translate of `f` by `g` is a stable
  value of `f` at `g`.

The extension is not claimed to be nonzero or a Whittaker functional. Those
properties, the stabilization hypothesis `hall` itself, and the source's later
Fubini and dominated-passage argument for chosen sections are left to separate
statement and proof tasks.
