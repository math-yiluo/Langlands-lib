# Character localization of compact induction in p-adic unipotent groups

Worker 288 defines the closed proposition
`Langlands.Whittaker.CompactLocalizationStatement.{uF,uV}`. This is an
internal, derived specialization of the character-weighted integration
argument in Bernstein–Zelevinsky (1977), not a literal quotation of its
normalized functor statements. The module states the target and proves
no localization equivalence.

## Exact scope

For every prime `p`, with `Fact p.Prime`, and every
`F : PadicField.{uF} p`, install `F.canonicalTopologicalData.topology`.
For every natural number `n`, let
`U = GeneralLinear.upperUnipotent (n + 1) F.Carrier`.
This is the actual upper-unitriangular matrix subgroup of `GL_(n+1)(F)`,
with the inherited topology and the topological group structure obtained
from `F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)`.
The rank-one case `n = 0` is included.

Quantify every subgroup `H : Subgroup U` whose underlying subset is closed,
every `V : Type uV` with `AddCommGroup V` and `Module ℂ V`, every smooth
representation `σ : Representation ℂ H V`, and every
`θ : Induction.SmoothCharacter ℂ U`. The subgroup `H` has its inherited
topology. The character is an actual homomorphism `U →* ℂˣ` with open
kernel. Neither nontriviality nor unitarity of the character is imposed.
The coefficient space has no topology. The field universe `uF` and
coefficient-space universe `uV` are independent.

Write `χ = θ.toMonoidHom` and let `Q(K, ρ, η)` denote the existing
`Jacquet.Localization.Coinvariants ρ (⊤ : Subgroup K)
  (η.comp (⊤ : Subgroup K).subtype)`. This notation is explanatory only;
the Lean statement uses the existing construction directly. The conclusion is

\[
 \operatorname{Nonempty}\!\left(
 Q(U,\operatorname{cInd}_H^U\sigma,\chi)
 \simeq_{\mathbf C}
 Q(H,\sigma,\chi|_H)\right).
\]

Here `cInd` is exactly `Induction.compactInduced H σ`. Its vectors are
actual covariant functions with a uniform open right stabilizer and
compact support modulo `H`; covariance is `f(hg) = σ(h) f(g)` and the
ambient action is right translation `(ρ(u)f)(x) = f(xu)`. Both `Q` spaces
are the actual quotients by the complex span of
`ρ(k)v - (η(k) : ℂ) • v`. The source carrier is in
`Type (max uF uV)` and the target carrier in `Type uV`.

The conclusion asserts a full complex linear equivalence. There is no
admissibility, finite generation, finite dimension, irreducibility, or
nonzero-module assumption. There are no supplied Haar measures,
unimodularity certificates, compatible quotient measures, exactness,
bijectivity, orbit geometry, or comparison hypotheses. No normalizer
action, naturality, or preferred scaling of the equivalence is specified.

## Inverse-character convention and proof obligations

For an ambient representation `ρ`, ordinary coinvariants of the twist
`χ⁻¹ ⊗ ρ` use generators

\[
 \chi(u)^{-1}\rho(u)v-v
   = \chi(u)^{-1}\bigl(\rho(u)v-\chi(u)v\bigr).
\]

The scalar is invertible, so these generators span the same relation
space as the specified character quotient. The corresponding induction
twist sends a function `f` to `g ↦ χ(g)⁻¹ • f(g)`, which has covariance
for `(χ|_H)⁻¹ ⊗ σ`. Thus the ordinary compact-induction coinvariant
integral must be applied to the **inverse-character twist**.

In terms of the original functions and the target character-quotient
projection `q`, the expected map has the formula

\[
 [f]\longmapsto
 \int_{H\backslash U}\chi(u)^{-1}\,q(f(u))\,d\nu(Hu).
\]

The weight cancels the left covariance after projection; right translation
by `a` multiplies the integral by `χ(a)`, agreeing with the positive
character in the relation `ρ(a)f - χ(a) • f`. This formula explains the
sign convention; the present proposition neither defines this integral
nor assumes its bijectivity.

A later proof must supply all measure facts for this concrete `U` and
every closed `H`. The existing compact-open containment theorem
`RankinSelberg.unipotent_exists_compact_open` suggests deriving
unimodularity of `H` by intersecting compact open subgroups of `U` with
the closed subgroup, then using Haar uniqueness. The published
`QuotientIntegration.compatibleMeasureExists` supplies compatible
quotient measures once its hypotheses have been established. These
measure deductions, the induction-twist transport, and the passage from
ordinary integral bijectivity to the displayed equivalence are proof
obligations, not hypotheses of this statement.

The separate published target
`Induction.CompactCoinvariantIntegralBijective` concerns a supplied
ordinary integral under explicit measure hypotheses. This module does
not restate that target or prove it. The existing induction and
localization definitions are imported unchanged.

## Original source and provenance

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. ENS (4) **10** (1977), 441–472,
§§1.7–1.9 (printed pp.443–445, with the measure discussion on p.444)
and §5.17 (printed pp.466–467).
Registered source: `bernstein-zelevinsky-1977-induced-i`.
Retained file:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
SHA256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The cited sections were read at PDF pages 4–6 and 27–28; printed
pp.444–445 and 466–467 were also visually checked. No source-specific
erratum was found in the checked current Library notes, project notes,
or literature index.

Section 1.7 explains invariant quotient measures when ambient and closed
subgroup modular characters are trivial. Section 1.8 defines compact
induction by right translation and localization by the relation span
used here, within its normalized functor framework. Section 1.9
discusses limits of compact subgroups, unimodularity, exactness, and
character twisting.

Section 5.17 integrates `ψ⁻¹(v)` times the projected induced function
over `V' \ V`. For the isomorphism argument it reduces to trivial
normalizer `N`, subgroup `M = V'`, and then trivial character by replacing
the inducing representation by its inverse-character twist. The next
page treats regular representations, direct sums, and free resolutions,
using exactness. In the present specialization its ambient `V` becomes
our `U`, its `V'` becomes `H`, and its coefficient space `L` becomes our
coefficient space `V`. Trivial normalizer leaves only the underlying
linear quotient equivalence; no modulus action is retained.

The exact canonical p-adic matrix realization, arbitrary closed-subgroup
scope, independent universes, and measure-free telescope are this
module's derived formulation. The source's argument motivates it;
this statement module does not formalize that argument.
