# Canonical field, character and Fourier conventions for LLC

Author: Worker 7. This construction specializes published mathematical objects
to every actual `F : Langlands.PadicField p`, for every prime `p` and arbitrary
field-carrier universe. It is one concrete prerequisite of the full
correspondence specification, not an assertion of LLC or of the existence of a
self-dual measure.

The only mathematical inputs are the prime condition and the algebraic finite
extension `F`. The module uses the constructed
`F.canonicalTopologicalData.topology`, its certified local-field structure, and
the actual Borel measurable structure of that topology. No arbitrary topology,
valuation model, measurable structure, or presumed analytic theorem is passed
into these declarations.

The two needed separation certificates are proved intrinsically. Hausdorffness
uses the selected additive-group uniformity and its local-field structure.
Total disconnectedness uses the nonarchimedean spectral norm and Mathlib's
ultrametric total-separation theorem. The Borel-space certificate is reflexivity
for the selected Borel measurable structure. These proofs introduce no
additional hypotheses on `F`.

`QuasiCharacter F` is the common `HarmonicAnalysis.Quasicharacter F.Carrier`.
It consists of all continuous homomorphisms `Fˣ → ℂˣ`, with the usual complex
topology and no unitarity restriction. This is an abbreviation for the existing
type, not a second character structure.

`NontrivialAdditiveCharacter F` is the common
`HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`: a continuous
nontrivial additive character with values in the unit circle.
`LocalTestFunction F` is the actual complex vector space of compactly
supported locally constant functions. `LocalAdditiveHaarMeasure F` is the
common bundle of regular additive Haar measures on the canonical Borel space;
it has no Fourier normalization field.

`localFourierTransform F ψ μ` is the actual linear map

\[
 f\longmapsto\left(y\longmapsto
 \int_F\psi(xy)f(x)\,d\mu(x)\right).
\]

The complex-valued realization of the circle-valued character is the common
one already constructed in `HarmonicAnalysis.Basic`. The plus sign and the
field product pairing are literal parts of the imported formula. Its input
is the test-function space, on which integrability was proved upstream.
Its output is an arbitrary function; this module does not assume a theorem
that the transform preserves the test-function space.

`IsSelfDualMeasure F ψ μ` is the common intrinsic self-duality proposition
specialized to this actual field and Borel space. It requires convergence of
the second Fourier integral for every test function and asserts that Fourier
squared is reflection `f(x) ↦ f(-x)`. It does not assert that such a measure
exists, choose one by an assumed existence field, or specify a possibly
incorrect scalar multiple of an arbitrary Haar measure. Those existence,
uniqueness and explicit-volume results remain separate proof obligations.

In the eventual correspondence predicates, one correspondence family must
satisfy the separate pair L- and epsilon-factor compatibilities for every
`NontrivialAdditiveCharacter F`. This module supplies that concrete common
character domain. It does not define either side's factors by the desired
compatibility. It also introduces no numerical norm: the residue-normalized
norm required by LLC is separate from the base-extending spectral norm that
constructs the topology.

## Original sources and implementation provenance

The specialization is internal interface work, using the published constructors
without changing their formulas or introducing theorem assumptions.
`Langlands.LocalField.Canonical` supplies the actual canonical realization.
`Langlands.HarmonicAnalysis.Basic` supplies the character, function, measure
and Fourier objects and their intrinsic construction proofs. They are imported,
not copied or re-proved.

- Henniart 2000, section 1.1, printed page 439, fixes arbitrary finite extensions
  of `Q_p` and the complex smooth representation setting. Sections 1.2–1.3
  specify the additive-character-dependent pair factors.
  Original `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- Tate 1979, section 3.2, printed page 13, gives the nontrivial additive
  character, the additive and multiplicative Haar measures and the Fourier
  pairing `ψ(xy)`. Its functions there are continuous functions with
  exponential decay; it is not the source of the test-function space.
  Section 3.6, printed page 17, gives the self-dual normalization in the local
  constants. Original `tate-1979-number-theoretic-background`, retained
  Corvallis Part II volume, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`;
  printed page `p` is PDF page `p+9`.
- Deligne 1973, sections 3.1–3.3, internal/PDF page 26, printed page 526,
  gives continuous quasi-characters, Haar measures and the plus-sign Fourier
  convention. Section 3.3 on that page also gives the test functions: smooth
  (`C^∞`) functions of compact support on the local field. For nonarchimedean
  `F` these are exactly the compactly supported locally constant functions
  used by `LocalTestFunction F`. Original `deligne-1973-local-constants`,
  SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.

These original passages were read for this task's source audit. The scalar
Haar-volume correction discussed in that audit is not needed to define this
intrinsic relation and is not silently replaced by Tate's disputed printed
ratio. The formalization uses the full integral relation above.

## Checked implementation inputs

The direct project inputs are the Library modules
`Langlands.LocalField.Canonical` and `Langlands.HarmonicAnalysis.Basic`, as
published at Library `9173b91d7bd642075001f7d8d56e9e6d26cae822`. Their paired
files have the following SHA-256 fingerprints:

| File | SHA-256 |
| --- | --- |
| `Langlands/LocalField/Canonical.lean` | `e702bb7808fc344bda47a3093d9438d5cda71dcb165be7110be7b393f61d7c48` |
| `Langlands/LocalField/Canonical.md` | `94a7a93a2ac19a6c106542cd76530caf8244892f29b98eea8755b031ec7e872d` |
| `Langlands/HarmonicAnalysis/Basic.lean` | `2198cecae146fa7f904dc2c01169d6321aee8e155c99614ed92f861fd2d65aff` |
| `Langlands/HarmonicAnalysis/Basic.md` | `770a9f6e068d76d72fb10ff91ee1a27b66696ebf0c52af23464fb4d0956ffdf6` |

The additional Mathlib import is
`Mathlib.Topology.MetricSpace.Ultra.TotallySeparated`, in the pinned Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435` with Lean 4.34.0.
Every imported project definition is present in this Library; no unreviewed
draft import is needed for this pair.

Compilation in the project Lean service completed without errors or warnings
on 2026-10-21, against the Library above. The axioms used are `propext`,
`Classical.choice` and `Quot.sound`.
The elaborated types of all six declarations were printed with universes.
The unapplied `@IsSelfDualMeasure` was checked against the complete telescope
`{p : ℕ} → [Fact p.Prime] → (F : PadicField.{uF} p) →
NontrivialAdditiveCharacter F → LocalAdditiveHaarMeasure F → Prop`.
No topology, measure-normalization witness or analytic theorem appears as a
hidden parameter. The inspection command also completed with exit code zero.
Independent semantic acceptance and publication remain necessary.
