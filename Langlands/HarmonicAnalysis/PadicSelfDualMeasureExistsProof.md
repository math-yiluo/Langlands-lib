# Scalar self-dual Haar existence

Author: Worker 688.

The theorem `Langlands.HarmonicAnalysis.padicSelfDualMeasureExists.{u}`
proves exactly the published
[PadicSelfDualMeasureExistsStatement](PadicSelfDualMeasureExistsStatement.md).
Its complete telescope is

```lean
theorem Langlands.HarmonicAnalysis.padicSelfDualMeasureExists
    {p : ℕ} [Fact p.Prime]
    (F : Langlands.PadicField.{u} p) (T : F.TopologicalData) :
    Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsStatement F T
```

The universe `u` is arbitrary. Every supplied `T` is covered, with no extra
hypotheses. The result gives a total-disconnectedness certificate for that
topology and, for each actual continuous nontrivial unitary additive character,
a regular additive Haar measure satisfying the existing `IsSelfDual` predicate.
In particular, it proves both convergence of the second Fourier integrand at
every argument and the equation that Fourier squared is reflection.

## Objects and dependencies

The proof installs the topology, valuative relation and local-field structure
from `T`. It uses their right additive uniform space and the corresponding
uniform-additive-group certificate, and the Borel measurable space of the
same topology with its `BorelSpace` certificate, exactly as the target does.
The first conjunct of the published `padicLatticeGeometry F T` supplies the
explicit total-disconnectedness conclusion and its local instance.

For a character `ψ`, write

```text
n = T.additiveConductor ψ,
L_m = T.additiveLattice m = π^(-m) O_F,
I_(m,a)(z) = 1 if z - a belongs to L_m, and 0 otherwise.
```

The indicators are raw complex-valued functions. The character is the bundle
`UnitaryAdditiveCharacter`; `ψ.complex` is its complex-valued additive
character. The measures are the existing regular `AdditiveHaarMeasure`
bundles, and both Fourier transforms use the plus-sign Bochner integral
`fourierIntegral ψ μ g y = ∫ z, ψ.complex (z*y) * g z ∂μ.measure`
from [Basic](Basic.md).

The proof imports the target and these published proof modules:

- [PadicLatticeHaarProof](PadicLatticeHaarProof.md): the second conjunct of
  `padicLatticeHaar F T`, applied to `ψ`, gives a regular additive Haar measure
  `μ` for which the real lattice masses satisfy
  `μ(L_m).toReal * μ(L_(n-m)).toReal = 1` for every integer `m`.
  That theorem constructs the measure by positive rescaling and proves the
  masses finite; it assumes no Fourier inversion.
- [PadicLatticeFourierProof](PadicLatticeFourierProof.md):
  `padicLatticeFourier F T` proves integrability and the exact Fourier formula
  for every raw lattice-coset indicator, every argument and every Haar measure.
  Its annihilator calculation uses the independently proved
  [PadicAdditiveConductorProof](PadicAdditiveConductorProof.md).
- [PadicLatticeSchwartzExpansionProof](PadicLatticeSchwartzExpansionProof.md):
  `padicLatticeSchwartzExpansion F T` expresses each Schwartz–Bruhat function
  as a finite complex linear combination of coset indicators at one common
  lattice level. All finite data are chosen before the argument.

The [PadicLatticeGeometryProof](PadicLatticeGeometryProof.md) module is imported
transitively by these proofs. All four prerequisite theorems cover arbitrary
`u` and supplied `T`. This module combines their proved conclusions and
introduces no additional statement interface.

## Implemented proof

First, the private theorem `fourierIntegral_finite_linear_combination` proves
linearity of the raw Fourier integral on a finite combination at a fixed
argument. It assumes integrability of each summand's Fourier integrand.
Distributing the character factor and commuting the complex coefficient
reduces the claim to `integral_finsetSum` and `integral_const_mul`.
Integrability of the scaled summands is supplied by `Integrable.const_mul`.

For the normalized measure above, the local binding `M m` is the complex
cast of `(μ.measure L_m).toReal`. The local lemma `hI` is the published
coset formula, rewritten using the centre-zero indicator:

```text
Integrable (z ↦ ψ(z*y) I_(m,a)(z)),
Fμ(I_(m,a))(y) = M_m ψ(a*y) I_(n-m,0)(y).
```

Here `Fμ` denotes `fourierIntegral ψ μ`, and `ψ` in formulas is understood
through its complex coercion. The helper `hzero` identifies `I_(k,0)` with
the indicator of `L_k`. The Haar mass product, cast to `ℂ`, is
`M_m M_(n-m) = 1` (`hmass`).

The local lemma `htwice` proves both second-integrand convergence and
reflection for each `I_(m,a)`. At an argument `x`, additive-character
multiplicativity and field commutativity give the pointwise identity

```text
ψ(y*x) Fμ(I_(m,a))(y)
  = M_m ψ(y*(x+a)) I_(n-m,0)(y).
```

The right side is a constant multiple of the first Fourier integrand for
`I_(n-m,0)` at `x+a`. Applying the integrability part of `hI` at that
complementary level proves integrability of the second integrand; an
everywhere equality is used through `Integrable.congr`.

The same pointwise identity and `integral_const_mul`, followed by the value
part of `hI` at level `n-m`, give

```text
Fμ(Fμ(I_(m,a)))(x)
  = M_m M_(n-m) I_(n-(n-m),0)(x+a)
  = I_(m,0)(x+a)
  = I_(m,a)(-x).
```

The centre-zero phase is `ψ(0)=1`. The integer identity `n-(n-m)=m` and
`hmass` give the middle equality. For the last equality, membership of
`x+a` in the additive subgroup `L_m` is equivalent to membership of
`-x-a = -(x+a)` in `L_m`. This explains the reflected argument for the
plus-sign convention, including arbitrary negative lattice levels.

Now let `f : SchwartzBruhat F.Carrier`. The published expansion supplies
integers and finite data `m, N, c, a` such that, at every point `z`,

```text
f(z) = ∑ i : Fin N, c_i I_(m,a_i)(z).
```

Function extensionality gives this equality of raw functions. The private
finite-linearity lemma and the first integrability clause of `hI` show
pointwise that

```text
fourierTransform ψ μ f = ∑ i, c_i Fμ(I_(m,a_i)).
```

For every second-transform argument, each summand's second integrand is
integrable by `htwice`. Scalar multiplication and `integrable_finsetSum`
give integrability of their finite sum; the displayed transform formula
identifies it with the required second Fourier integrand. This is the first
clause of `IsSelfDual ψ μ`.

Apply finite linearity once more to that transform formula, using precisely
these second-integrand integrability proofs. The reflection clause of
`htwice` then gives

```text
fourierIntegral ψ μ (fourierTransform ψ μ f) x
  = ∑ i, c_i I_(m,a_i)(-x)
  = f(-x).
```

This proves the second clause of `IsSelfDual ψ μ`. The witness `μ` depends
only on `ψ`; it was chosen before `f`. Together with the supplied-topology
total-disconnectedness certificate this proves the target.

## Provenance and original-source comparison

This is a derived assembly proof of the existing focused proposition. It
uses actual valuation lattices, Haar measures, characters and Bochner
integrals. It proves the needed inversion directly on lattice cosets and
finite sums. It assumes neither a general inversion theorem nor
`IsSelfDual`, and uses no local-factor functional equation.

Worker 688 read the following registered retained originals:

- André Weil, *Basic Number Theory*, second edition (1973), source
  `weil-1973-basic-number-theory`, retained file
  `/home/taskhub/central-library/Weil--Basic number theory (book, 2nd edition)--1973.pdf`,
  SHA-256
  `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
  Chapter II §5, Theorem 3 and its corollary, Definition 4 and Proposition 12,
  printed pp.40–42 / PDF pp.57–59, give the pairing, conductor convention
  and dual lattice. Chapter VII §2, printed pp.104–108 / PDF pp.121–125,
  gives the plus-sign transform, self-dual measure, standard functions,
  Proposition 2's finite coset calculation, and its three corollaries.
  The formula (2) on p.107 and Corollary 3 on p.108 were also visually
  checked in the retained page images.
- John Tate, *Number theoretic background*, Corvallis Part II (1979),
  source `tate-1979-number-theoretic-background`, retained file
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
  SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  Section 3.2 and (3.2.6), printed p.13 / PDF p.22, give the same Fourier
  sign and conductor. Section 3.6, printed p.17 / PDF p.26, uses self-dual
  Haar measure; the scalar-ratio sentence was also visually checked.
- Pierre Deligne, *Les constantes des équations fonctionnelles des
  fonctions L* (1973), source `deligne-1973-local-constants`, retained file
  `/home/taskhub/central-library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`,
  SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
  Sections 3.1 and 3.3, internal/PDF p.26 / printed p.526, fix the same
  character and plus-sign Fourier conventions.

Weil introduces self-dual measure through general dual-group Fourier
inversion on p.105. The Lean proof instead uses the published, independently
proved normalized Haar construction and verifies inversion by the explicit
calculation above. Its finite expansion and single-coset formula follow the
route of Weil's Proposition 2 and formula (2). The reciprocal masses match
Corollary 1, and the normalization of the imported Haar witness matches
Corollary 3: its integer-ring mass is `1 / sqrt(q^n)`.

The published [scalar-measure correction](../LocalFactor/Harmonic/Statement.md)
was read. Tate's sentence after (3.6.2) prints a negative exponent for the
fixed-Haar to self-dual scalar ratio. The correction uses the positive
exponent, consistent with Weil's integer-ring normalization. This proof
uses only the published reciprocal mass identity and no scalar-ratio
formula. No source-specific errata file for these three sources was found
in the checked workspace/project notes or retained literature on 2026-10-29.

The theorem asserts existence and Fourier-square reflection on the given
test space. Uniqueness of self-dual or dual measures, symmetry of duality
and the other conjuncts of `PadicFourierDualityStatement` are outside this
focused conclusion.

## Verification

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. Development compilation and a
Lake build of the proof and a private complete-telescope check succeeded
with no errors or warnings. The check assigns the complete unapplied
`@Langlands.HarmonicAnalysis.padicSelfDualMeasureExists` to the dependent
function type displayed above. Declaration inspection reports universe
parameter `u` and only `propext`, `Classical.choice` and `Quot.sound`.
The target and every existing Library Lean/Markdown pair are preserved.
Formal exact-target validation and independent semantic review are separate
acceptance and publication requirements.
