# Dual functional equations for ordinary local constants

This module states Deligne's ordinary and spectral dual equations on the actual
continuous exact virtual group of each finite intermediate field in a common
closure. All declarations are proposition definitions. It proves neither a
functional equation nor the existence of a local-constant system.

## Objects and quantifiers

The namespace is `Langlands.LocalFactor.NonabelianSystem`. Both equations quantify
over a prime, a finite p-adic base field `F`, a reciprocity family `e`, and an
assignment `ε` satisfying the already published `IsSystem F e ε`. They then
quantify over every finite intermediate field `E`, every continuous nontrivial
unitary additive character `ψ`, two regular additive Haar measures `μ, μ'`, and
every class `x : CommonClosure.Virtual F E`. The field and carrier universes are
independent outer parameters; the representation carrier is in `max uF uV`, as
required by the imported system.

The exact virtual group imposes genuine short-exact-sequence relations. Its
published `continuousDual` comes from actual contragredient representations,
with reversal of short exact sequences, quotient descent, continuity,
involution, and degree preservation proved in `ExactDual`. There is no
semisimplicity, positivity, irreducibility, or degree-zero restriction.

`FourierDualMeasures F E ψ μ μ'` is the concrete relation

\[
 \int_E \psi(xy)\left(\int_E\psi(tx)f(t)\,d\mu(t)\right)d\mu'(x)
 = f(-y)
\]

for every locally constant compactly supported complex test function `f` and
every `y`. The inner integral is the published plus-sign `fourierTransform`;
its integrability is proved in `HarmonicAnalysis.Basic`. The predicate also
requires integrability of each outer integral. Thus the relation cannot rely
on the default value of a divergent Bochner integral. Both measures use the
canonical topology of `E` and its Borel space.

This predicate names the dual-measure relation already written inline in
`LocalFactors.PadicFourierDualityStatement`, with explicit outer convergence.
It does not choose a dual measure. Existence, uniqueness, Fourier closure and
inversion are the separate harmonic-analysis statement family. Here the
relation identifies the supplied second measure in an epsilon identity; the
epsilon identity itself is not a hypothesis.

## Equations

`FixedHaarDualityStatement` states

\[
 \epsilon_E(x,\psi,\mu)\,
 \epsilon_E(x^\vee\otimes|\cdot|_E,\psi^{-1},\mu')=1
\]

whenever the supplied measures are Fourier dual. Here `ψ.scale (-1)` is precisely
`y ↦ ψ(-y)`, hence the inverse additive character. The character twist is
`ExactGrothendieckGroup.continuousTwist
(CommonClosureWeilDeligne.normCharacter F E)`. This norm character is the
restriction of the actual base Weil norm to the actual subgroup fixing `E`;
it is not an arbitrary unramified character. In particular it takes an
`E`-geometric Frobenius to `q_E⁻¹`.

`SpectralDualityStatement` states, for every complex `s`,

\[
 \epsilon_E(x,\psi,\mu,s)\,
 \epsilon_E(x^\vee,\psi^{-1},\mu',1-s)=1.
\]

These are the published `conditionalDeligneValue` values: epsilon is evaluated
on the actual spectral twist `x ⊗ |·|_E^s`. Its implementation uses the base
residue cardinality and the restricted base degree together; it does not
incorrectly renormalize the base degree to one on extension-field Frobenius.
All values are complex units. No rational L-factor, denominator, or value at a
meromorphic pole occurs.

`DualFunctionalEquationStatement` conjoins the two statements. Neither equation
is part of `IsSystem`; that imported specification and its separate existence
and uniqueness propositions are unchanged. The measures can differ. This
module does not replace them with a self-dual measure or insert a half shift.
The centered Langlands convention remains the distinct constructor in
`CommonClosureSpectral`.

## Original source and derived formulation

The source is Pierre Deligne, *Les constantes des équations fonctionnelles des
fonctions L* (1973), registered as `deligne-1973-local-constants`, SHA-256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.

- Section 3.3, retained PDF/internal page 26, printed page 526, defines the
  plus-sign Fourier transform.
- Formula (5.7.1), retained PDF/internal page 49, printed page 549, gives the
  product of epsilon for `V` and for `V* · ω₁`, with `ψ(-x)` and the Haar measure
  dual to the first measure relative to `ψ`. This is the first Lean equation.
- Formula (5.2), internal page 48, printed page 548, permits virtual `V`.
  The spectral convention immediately preceding (5.5.2) on that page defines
  the parameter by twisting by `ω_s`.
- The spectral equation is a derived restatement: apply (5.7.1) to
  `V ⊗ ω_s`, whose contragredient is `V* ⊗ ω_{-s}`, and then multiply the
  norm characters `ω_{-s} ω₁ = ω_{1-s}`. This reasoning explains the target;
  it is not implemented as a proof of either statement.
- The demonstration note on internal page 51, printed page 551, reduces
  (5.7.1) to characters and Fourier inversion. No such reduction is proved
  here.

## Validation and scope

The pinned Lean environment compiled the module without diagnostics and confirmed
that the aggregate declaration returns `Prop`. The submission imports the
published `ExactDual` module. This is a focused ordinary duality contribution;
conductor-exponent formulas, highly ramified stability, and Weil–Deligne
pair/block formulas remain separate statements. Compilation checks the target's
well-formedness; it proves neither dual functional equation.
