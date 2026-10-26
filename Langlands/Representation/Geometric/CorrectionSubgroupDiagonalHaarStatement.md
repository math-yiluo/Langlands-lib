# Diagonal Haar modulus on the full GL correction subgroup

`Langlands.Geometric.CorrectionSubgroupDiagonalHaarStatement.{uF}` is a
Prop-valued definition. It states an internal, derived actual-Haar calculation;
this module does not prove the formula.

For every prime `p`, every actual finite p-adic extension
`F : Langlands.PadicField.{uF} p`, every supplied `T : F.TopologicalData`, every
rank `n`, every pair `B C : Langlands.GeneralLinear.BlockShape n`, and every
permutation `w : Equiv.Perm (Fin n)`, put

```text
g = GeneralLinear.permutation n F.Carrier w
H = intersectionSource
      (B.unipotentSubgroup F.Carrier) (C.parabolic F.Carrier) g
A = { (a,b) : Fin n × Fin n |
      blockIndex B a < blockIndex B b ∧
      blockIndex C (w a) ≤ blockIndex C (w b) }.
```

`intersectionSource` is the published declaration in namespace
`Langlands.Geometric` (the closedness helper is in `Langlands.Geometric.General`).
Thus `H` is the actual ambient subgroup `U ∩ g⁻¹ Q g`, with
`U = B.unipotentSubgroup F.Carrier` and `Q = C.parabolic F.Carrier`.
The first condition in `A` selects the strictly upper block entries of `U`;
the second retains entries whose conjugates belong to the upper block
parabolic `Q`, including entries within one `C` block. The non-strict second
inequality is essential: the formula concerns the full correction subgroup.
The published `GeneralLinear.permutation_conjugate_entry` sends the entry
indexed by `(a,b)` to `(w a,w b)`, explaining this use of `w`.
`A` is defined inline as a finite subtype; no coordinate construction is an
input or import.

For every `t : Fin n → F.Carrierˣ` and every `d : Subgroup.normalizer H`, the
only additional hypothesis is the literal equality of matrices

```text
(d.val : Matrix (Fin n) (Fin n) F.Carrier)
  = Matrix.diagonal (fun i => (t i : F.Carrier)).
```

The asserted equality, in the positive units `ℝ≥0ˣ`, is

```text
HaarModulus.closedNormalizerCharacter H hH d
  = ∏ (a,b) : A, T.normalizedAbsUnits (t a) / T.normalizedAbsUnits (t b).
```

The definition installs exactly `T.topology`, `T.valuativeRel`, `T.localField`,
`T.fieldT2`, and `T.generalLinearLocallyCompactSpace n`. It constructs `hH`
internally using `General.isClosed_correctionSubgroup`,
`B.isClosed_unipotentSubgroup F.Carrier`, and `C.isClosed_parabolic F.Carrier`.
These closedness and topology facts are not extra hypotheses. Normalizer
membership is carried by `d` and supplies the domain of the actual character;
it supplies no Haar comparison. The field universe is arbitrary, the supplied
topological realization is retained, and no positive-rank or minimal-permutation
condition is imposed. Empty root sets use the empty product `1`.
There are no Haar-scaling, determinant-comparison, root-product, coordinate,
minimality, or cancellation hypotheses.

The case `C = B`, `w = 1` is intended to give the whole radical formula:
`U ≤ B.parabolic F.Carrier`, so `H = U`, and the second root condition is then
automatic. This specialization is explained here, not proved in this module.

## Actual Haar character and direction

The published construction
[`Langlands.Group.HaarModulus`](../../Group/HaarModulus.md) defines
`HaarModulus.closedNormalizerCharacter H hH` using the actual continuous
conjugation automorphism on the closed subgroup. With
`α(h) = d * h * d⁻¹` and `c` the underlying nonnegative-real value of this
character, its convention for a regular Borel Haar measure `μ` on `H` is

```text
c • μ.map α = μ.
```

This is `HaarModulus.normalizerCharacter_smul_map` after installing the
closed subgroup's local compactness and using `closedNormalizerCharacter_eq`.
Consequently the pushforward scale is `c⁻¹`. Equivalently, the integral of
`f (α⁻¹ h)` is `c` times the integral of `f h`. The right-hand side of the
statement is the modulus `c`, not the pushforward scale.

## Original source and derived provenance

The original is I. N. Bernstein and A. V. Zelevinsky, *Induced representations
of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472.
Section 1.7, printed pages 443–444 (PDF pages 4–5), defines the modulus by the
inverse-integrand convention and then defines the character of a subgroup's
normalizer by conjugation. Section 6.4, printed pages 468–469 (PDF pages 29–30),
reduces the correction calculation to the split case and the maximal torus.
On printed page 469 the unipotent modulus is the product of absolute values
of the corresponding roots, and opposite root products cancel. Section 6.4
was read in full; the root product and the convention were also checked on
the rendered original.

This definition is a derived specialization of that root calculation to the
Library's full GL correction subgroup, with roots `t a / t b` indexed by `A`.
It is not quoted as a separately numbered source theorem and does not state
the source's full geometric-lemma or correction-cancellation conclusion.
The source's minimal representatives enter its orbit calculation; the present
individual diagonal formula is stated for every permutation. Its proof remains
an obligation.

Literature ID: `bernstein-zelevinsky-1977-induced-i`.
Original file:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
SHA-256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

The intended analytic proof input is the published
[`Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`](../../HarmonicAnalysis/PadicScalarHaarScalingProof.md),
specifically `Langlands.HarmonicAnalysis.padicScalarHaarScaling`. For a field
unit `a`, it proves that multiplication by `a` pushes an additive Haar measure
forward by `(T.normalizedAbsUnits a : ℝ≥0)⁻¹`. A future proof must construct
actual allowed-entry coordinates for `H`, establish left invariance of the
transported product measure, compute diagonal conjugation as multiplication
by `t a / t b` in each coordinate, and identify the resulting scaling with
the actual normalizer character by Haar uniqueness. Neither that transport nor
that identification is assumed or proved here. The scalar result is cited as
an intended proof input and is not required to elaborate this statement.

Author: Worker 165.
