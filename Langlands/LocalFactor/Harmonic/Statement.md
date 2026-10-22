# Local Fourier inversion and Haar normalization

Placement note (Worker 64): the canonical module is `Langlands.LocalFactor.Harmonic.Statement`.
It is moved from `Langlands.LocalFactors.Harmonic.Statement` with every public declaration name,
namespace, type and mathematical body retained. The old module remains a thin
compatibility import. Original source references and authorship below are retained.
The [migration record](../Abelian/Definitions.md#structural-migration-record) gives the complete map and checks.


Worker 33 authors this theorem-statement family. It contains proposition
definitions, not proofs. The closing target is
`Langlands.LocalFactors.PadicHarmonicAnalysisStatement`.

## Actual objects and scope

Every component quantifies an arbitrary prime `p`, every universe-polymorphic
`F : Langlands.PadicField p`, and a supplied `T : F.TopologicalData`.
It uses that topology's Borel measurable space, the actual integer ring
`T.Integers`, its chosen uniformizer, actual residue cardinality
`T.residueCardinality`, and actual function `T.normalizedAbs`. The accepted
integer-valued order has `ord(0)=0`; the only order value used in a scaling law
is that of an explicit unit.

An additive character is Mathlib's `AddChar F.Carrier Circle`, with explicit
continuity and nontriviality hypotheses. The unit circle has its usual topology;
unitarity is built into its codomain. A Schwartz--Bruhat function is concretely
a complex-valued function that is locally constant and has compact support.
A Haar measure is a Borel `Measure` satisfying `IsAddHaarMeasure`. Finite
extensions of the p-adics with their supplied module topology are second
countable, so Mathlib's Haar definition has the usual regularity here.
No abstract factor symbols, measure axioms, or existence assumptions substitute
for these objects.

Mathlib's `Fourier.fourierIntegral χ μ` uses `χ(-x*y)`. We therefore use
`Fourier.fourierIntegral ψ⁻¹ μ` throughout. The first target includes its exact
equality with the plus-sign integral

```
FT[ψ,μ](f)(y) = ∫ ψ(x*y) f(x) dμ(x).
```

The temporary `dual` and `conductor` expressions inside the propositions are
ordinary local `let` expressions. They do not declare competing bundled
character, test-function, Fourier-transform, or local-constant constructions.
The self-dual existence clause reuses the companion's actual
`Langlands.HarmonicAnalysis.SelfDualMeasureExists`, and uniqueness uses its
`IsSelfDual` predicate. The raw integral formulas are retained as explicit
Mathlib interfaces and their equivalence to the companion predicate is a
conclusion. There is no second self-dual-measure construction.

## The five components

1. `PadicFourierClosureStatement` asserts integrability of test functions and
   their Fourier integrands, the plus-sign identity, preservation of local
   constancy and compact support, and integrability of the transform. Thus the
   statements do not exploit Mathlib's totalization of a divergent integral.
2. `PadicFourierDualityStatement` first asserts total disconnectedness of the
   supplied field topology as a conclusion. With that certificate, it reuses
   `SelfDualMeasureExists` for existence, asserts uniqueness using `IsSelfDual`,
   and identifies that predicate with the raw Fourier inversion equation.
   It also asserts existence and uniqueness of the dual Haar measure for every
   fixed Haar measure and symmetry of duality. The defining raw equation is
   `FT[ψ,ν](FT[ψ,μ](f))(x)=f(-x)` on every test function. Inversion is a conclusion,
   not a hypothesis of its own existence theorem.
3. `PadicFourierScalingStatement` gives additive Haar scaling on measurable
   sets, linear scaling of the transform when Haar measure is multiplied by a
   positive scalar, the character change `ψ_a(x)=ψ(a*x)`, and the argument-change
   formula
   `FT[ψ,μ](f(a*·))(y)=|a|_F⁻¹ FT[ψ,μ](f)(a⁻¹*y)`.
   Here `|a|_F` is the actual residue-cardinality normalization, not the
   base-extending spectral norm.
4. `PadicAdditiveConductorStatement` asserts existence and uniqueness of the
   largest integer `n` on whose fractional ideal `π^(-n) O_F` the character is
   trivial. It gives `n(ψ_a)=n(ψ)+ord_F(a)` and identifies the annihilator of
   the actual integer ring with `π^(-n) O_F`. The conductor is not an arbitrary
   integer chosen to force the volume formulas.
5. `PadicFourierNormalizationStatement` identifies dual measures by
   `μ(O_F)ν(O_F)=q^(-n)`, and self-dual measures by `μ(O_F)=q^(-n/2)`.
   It gives the integer-ring indicator transform, the fixed-Haar to self-dual
   ratio, and the self-dual change of measure
   `μ_(ψ_a)=|a|_F^(1/2) μ_ψ`. Measures themselves take extended nonnegative
   values; finite integer-ring volumes are converted with `.toReal` where
   products of real or complex numbers are required.

The family treats the nonarchimedean local harmonic prerequisites. It does
not claim to formalize the abelian zeta functional equation, epsilon systems,
Weil--Deligne factor identities, highly ramified stability, or archimedean
factors. Those remain parts of the parent assignment.

## The scalar-measure discrepancy

With the convention in Tate (3.2.6) and Deligne (3.4),
the annihilator of `O_F` is `π^(-n(ψ)) O_F`. Its Haar volume is
`q^(n(ψ)) μ(O_F)`. Applying Fourier inversion to the integer-ring indicator
therefore yields

```
μ_ψ(O_F) = q^(-n(ψ)/2),
μ / μ_ψ = q^(n(ψ)/2) μ(O_F).
```

The second formula uses the positive exponent. The retained original Tate
page 17, immediately after (3.6.2), instead prints a negative exponent in
the formula for `dx/dx_ψ`. We do not transcribe that sentence. Weil,
Chapter VII §2, Proposition 2, Corollary 3, page 108, explicitly gives the
self-dual integer-ring volume as `mod(a)^(1/2)` for `ord(a)=n(ψ)`, hence
`q^(-n(ψ)/2)`. His proof uses the actual annihilator and the identity
`μ(O_F)μ(O_F^⊥)=1`. This verifies the correction from the original Fourier
definitions, independently of any epsilon-factor convention.
Worker 33 visually checked both original pages.

For example, scaling a conductor-zero character by a uniformizer makes
`n(ψ)=1`. Its self-dual integer-ring volume becomes `q^(-1/2)`, and a
fixed measure assigning volume one has ratio `q^(1/2)`. This also agrees
with `μ_(ψ_a)=|a|_F^(1/2)μ_ψ`.

## Sources and correspondence

- Andre Weil, *Basic Number Theory*, second edition, Springer, 1973.
  Literature ID `weil-1973-basic-number-theory`;
  SHA256 `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
  Retained file:
  `C:/Central-Library/Weil--Basic number theory (book, 2nd edition)--1973.pdf`.
  Chapter II §5, Theorem 3 and its corollary, Definition 4 and Proposition 12,
  printed pp.40–42 / PDF pp.57–59, supply the field self-duality, conductor
  convention, and annihilator calculation. Chapter VII §2, printed
  pp.104–108 / PDF pp.121–125, supplies the plus Fourier convention, Lemma 1's
  change of variables, dual/self-dual measure existence and uniqueness,
  Definition 1's test functions, and Proposition 2 with Corollaries 1–3.
  These are the direct sources for the five targets.
- John Tate, *Number theoretic background*, Corvallis Part II (1979), pp.3–26.
  Literature ID `tate-1979-number-theoretic-background`;
  SHA256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  Retained file:
  `C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
  §3.2, pp.13–14 / PDF pp.22–23 fixes the Fourier sign and conductor.
  §3.6, p.17 / PDF p.26 fixes self-dual measure and the half-shift convention;
  the scalar sentence after (3.6.2) requires the correction above.
  No epsilon theorem is asserted in this contribution.
- Pierre Deligne, *Les constantes des equations fonctionnelles des fonctions L*
  (1973). Literature ID `deligne-1973-local-constants`;
  SHA256 `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
  Retained file:
  `C:/Central-Library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`.
  §3.3–3.4, internal/PDF pp.26–28, gives the same Fourier and conductor
  conventions. §5.7, internal/PDF pp.49–50, and its explanation on p.51
  use dual Haar measure and Fourier inversion in the local dual equation.
  These locators explain the intended connection, without importing
  Deligne's constant-system existence theorem as a premise.

## Exact dependencies and validation boundary

The arithmetic project import is
`Langlands.LocalField.Normalization.Definitions`, artifact
`e3d7bbd4-f2b9-4970-a60f-bf6aa0b34bb2` version 1, accepted, published,
and verified current. Its underlying field definition is artifact
`ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0` version 1.
No unproved normalization theorem is imported as a proof assumption.

The shared harmonic import is Worker 20's accepted
`Langlands.HarmonicAnalysis.Basic`, artifact
`65988160-6fd5-4d2d-9c21-0976b2137010` version 1. Its current publication was
verified at Library commit `843c574c920aa9926ab56adf662c74b3cd4ed0e1`,
including the complete final review receipt
`3dcce1a7f7fa421db3d03a1bc8ecdcd6` and the effective integrated pair.
Its Lean SHA256 is
`2198cecae146fa7f904dc2c01169d6321aee8e155c99614ed92f861fd2d65aff`.
Its effective Markdown SHA256 is
`770a9f6e068d76d72fb10ff91ee1a27b66696ebf0c52af23464fb4d0956ffdf6`.
The Lean dependency is unchanged from the checked development version. Both
local-field definition dependencies above were also fetched as accepted,
published and current at that same Library commit, with their previously
reviewed effective Lean/Markdown hashes unchanged.
It uses the companion's bundled existence predicate without treating its
unproved existence assertion as a hypothesis. The topology, compatible additive
uniformity, and Borel structure are installed locally from supplied or Mathlib
constructed data; no extra topology or total-disconnectedness premise is added.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1:
Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
Mathlib supplies the actual Bochner integral, additive characters, Haar
predicate, locally constant functions, compact support, and real powers.
The earlier Mathlib-only formulation passed development compilation and
whole-target fingerprint inspection, diagnostic
`51a8ef8b-cdfe-49a7-a05d-501fb6a8a825`. That fingerprint is superseded by the
alignment with the companion's predicates; it must not be used to submit
this revised source. The revised source passed a fresh full development check
`0a5c9682-b469-4e45-8dda-1b1e9a832a11`: all four modules compiled with no
warnings or errors, and inspection confirmed a universe-polymorphic `Prop`
definition. Its checked target fingerprint is
`96cb5af71f21e075cad111e69a8f9db3c6af1a2f97c23eefe3408ed892da277e`.
The fingerprint matches the earlier conjunction expression because its named
component references are unchanged; this does not mean their definitions or
the dependency bytes are unchanged. The new source snapshot and fresh check
are the relevant evidence. Only `propext`, `Classical.choice`, and `Quot.sound`
occur among the inspected target assumptions. The checked statement and
imported Lean bytes are unchanged, so the successful exact check remains
applicable. Independent semantic review and publication of this statement
remain outstanding. This contribution supplies no theorem proof.
