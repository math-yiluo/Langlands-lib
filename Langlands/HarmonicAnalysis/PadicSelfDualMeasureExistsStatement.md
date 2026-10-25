# Scalar self-dual Haar existence for a supplied p-adic topology

Worker 458 authored this focused proposition definition.
`Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsStatement.{u}` has
implicit parameters `{p : ℕ}` and `[Fact p.Prime]`, followed by explicit
parameters `(F : Langlands.PadicField.{u} p)` and `(T : F.TopologicalData)`.
It returns `Prop` for arbitrary field universe `u` and every supplied `T`.

The proposition installs `T.topology`, `T.valuativeRel`, and `T.localField`.
It uses the compatible right additive uniform space and its uniform-additive-group
certificate, and the Borel measurable space of that same topology with its
`BorelSpace` certificate. Local compactness, the Hausdorff property, and the
topological-ring structure come from the supplied local-field data. It then
asserts existence of `htd : TotallyDisconnectedSpace F.Carrier` and, using
that certificate, states

```text
∀ ψ : UnitaryAdditiveCharacter F.Carrier, SelfDualMeasureExists ψ.
```

Thus total disconnectedness is an explicit conclusion, rather than an additional
instance hypothesis. The character is the actual bundled continuous nontrivial
unit-circle-valued additive character from [Basic](Basic.md). The existing
`SelfDualMeasureExists` predicate is reused unchanged: it asserts existence of a
regular additive Haar measure `μ` satisfying `IsSelfDual ψ μ`. For each compactly
supported locally constant complex function `f`, that predicate requires the
second Fourier integrand to be integrable at every argument and requires

```text
∫ x, ψ.complex (x * y) * fourierTransform ψ μ f x ∂μ.measure = f (-y).
```

Both transforms are the actual plus-sign Bochner integrals defined in `Basic`.
Neither self-dual existence nor an abstract Fourier inversion axiom is a premise.
The statement does not choose a character or a measure.

## Derived provenance and scope

This is an internal specialization of
`Langlands.LocalFactors.PadicFourierDualityStatement` in
[Local Fourier inversion and Haar normalization](../LocalFactor/Harmonic/Statement.md).
At each `p`, `F`, and supplied `T`, it retains that statement's total-disconnectedness
conclusion and its `SelfDualMeasureExists` conjunct, expressed directly for the
bundled characters. Conversely, each bundled character provides precisely the
`AddChar`, continuity proof, and nontriviality proof quantified in the larger
statement. This explains the specialization; it supplies no existence proof.
The module imports only the local-field definitions and common harmonic objects.

The focused target is the scalar existence obligation needed before applying
finite-row Fourier results under a supplied scalar `IsSelfDual` measure. It
asserts no uniqueness of dual or self-dual measures and no symmetry of duality.
Generic scalar Fourier closure and sigma-finiteness, and finite-row compatibility,
remain separate proof obligations. This statement does not prove the larger
`PadicFourierDualityStatement` or assume local-factor functional equations,
common generators, or span results.

## Original sources

- Andre Weil, *Basic Number Theory*, second edition, Springer, 1973,
  Chapter II §5, Theorem 3 and its corollary, printed pp.40–41 / PDF pp.57–58,
  identify the additive field with its character dual through any nontrivial
  continuous character and the pairing `ψ(x*y)`. Chapter VII §2, printed
  pp.104–105 / PDF pp.121–122, gives the plus-sign Fourier transform, dual
  measure and the self-dual Haar normalization. Definition 1 and Proposition 2
  with Corollary 2, printed pp.106–108 / PDF pp.123–125, identify the
  nonarchimedean test functions and ensure their Fourier integrability.
  Registered source `weil-1973-basic-number-theory`, retained file
  `/home/taskhub/central-library/Weil--Basic number theory (book, 2nd edition)--1973.pdf`,
  SHA256 `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
- John Tate, *Number theoretic background*, Corvallis Part II (1979),
  §3.2, printed p.13 / PDF p.22, fixes the same Fourier sign; §3.6,
  printed p.17 / PDF p.26, uses self-dual Haar measure.
  Registered source `tate-1979-number-theoretic-background`, retained file
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
  SHA256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  The larger statement's Markdown records the scalar-ratio exponent discrepancy
  after Tate (3.6.2), checked against Weil VII §2, Corollary 3, p.108 / PDF p.125.
  This focused statement contains no scalar-ratio or conductor-volume formula.
- Pierre Deligne, *Les constantes des equations fonctionnelles des fonctions L*
  (1973), §3.1 and §3.3, internal/PDF p.26 (printed p.526), supplies the
  continuous-character and plus-sign Fourier conventions used by `Basic`.
  Registered source `deligne-1973-local-constants`, retained file
  `/home/taskhub/central-library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`,
  SHA256 `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.

Worker 458 read Weil PDF pp.57–59 and 121–125, Tate PDF pp.22–23 and 26,
and Deligne PDF pp.26–28. No source-specific errata file was present in the
workspace or public notes; the published scalar-ratio correction was read.
The bundled formulation, local instance setup, and explicit total-disconnectedness
conclusion are derived Lean packaging, rather than verbatim source notation.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
This module defines a proposition only and contains no proof of its target.
