# Actual dominant determinant slices under reversed duality

This internal definition and support-lemma unit transports the actual dominant
quotient kernels and their genuine convergence predicates across the published
lower quotient duality. The kernel comparisons retain the explicit premise
`TwoBlockDominantDualMatrixStatement`. The module neither proves that matrix
statement nor asserts convergence or either final dominant gamma/L proposition.

## Inputs and actual coefficients

The field `F : PadicField p` carries its canonical topology, valuation,
local-field and Borel structures. Its universe and the dependent block-carrier
universe are independent. The two positive block sizes `m i + 1` have sum
`t + 1`; each block representation `σ i` is smooth. No irreducibility,
nonvanishing functional, factor certificate or additional representation-type
assumption is imposed. The rank relation is `r = t + (j + k + 1)`; either
natural rectangle dimension may be zero. Thus this unit concerns the strictly
dominant case.

Write `E = reversedDualSectionEquiv F h σ hσ` for the actual equivalence chosen
before the character, functionals and analytic inputs. The reversed family
reverses the sizes, dependent carriers, additive and module structures, and
inverse-transpose block actions. Write `ellD i` for
`secondDualFunctional ψ (σ i.rev) (ell i.rev)`. The dual test is precisely
`reversedDualTest hr ψ Wtest`, the first dual Whittaker function translated by
the prescribed right Weyl element. Its rectangle dimensions are `k,j`.

The definition `reversedDualSliceCoefficient ... d` is the existing
`kernelSliceCoefficient` applied to `ellD`, `E f`, that translated dual test,
and the reversed size family. In particular it is the zero-parameter complex
quotient-kernel integral on the reversed lower determinant slice `d`.
`reversedDualNormProfileSliceCoefficient` uses the existing real
`kernelNormProfileSliceCoefficient` for the same inputs. That real coefficient
integrates the rectangle integral of the raw weighted kernel's norm; it is
not the norm of the complex coefficient.

Both definitions use the same supplied additive Haar measure `ν` for their
rectangle measures, and the same supplied standard quotient measure `νN`.
Their lower measures are exactly `lowerMeasure F (reverse_sum h) νN`, the
published pushforward of `νN` by the inverse block-rotation equivalence.
No measure normalization is selected.

## Exact slice measure transport

The transport lemmas assume right invariance `hN` of the canonical unipotent
Haar measure and compatibility `hνN` of the supplied standard quotient measure
with the canonical group and unipotent Haar measures. These are explicit
premises; no compatibility is inferred merely from a measure's type.

Let `D = TwoBlockLowerFourier.lowerDuality F.Carrier h`. Its representative
formula is `[g] ↦ [w_(t+1) * inverseTranspose g]`, and it sends determinant
order `d` to `-d`. The lemma `lowerDuality_restrict_measurePreserving` extracts
from the published `lowerDuality_measure_transport` the exact law

```text
D : ((lowerMeasure F h νN).restrict (lowerSlice h d))
      → ((lowerMeasure F (reverse_sum h) νN).restrict (lowerSlice (reverse_sum h) (-d)))
```

as a measure-preserving map. Here `lowerSlice` abbreviates the existing
`TwoBlockLowerUnipotentQuotient.determinantSlice`, only for this display.
This measure law has no matrix-identity premise and introduces no Haar scalar.

## Complementary parameters and genuine convergence equivalences

Assuming the explicit matrix statement, the imported actual kernel comparison
identifies the dual complex quotient kernel at `D q,1-s` with the original at
`q,s`. It separately identifies the real raw-norm profile and the actual
rectangle fiber-integrability predicate.

`setIntegral_quotientKernel_reversedDual` and
`setIntegral_quotientNormProfile_reversedDual` use the restricted
measure-preserving equivalence to pull back the two outer integrals, then apply
the corresponding pointwise identities. They are equalities of total Bochner
integrals for every complex `s` and integer `d`, without convergence hypotheses.

Genuine convergence is handled independently:

- `integrableOn_quotientKernel_reversedDual_iff` transports complex outer
  integrability between the reversed slice `-d` at `1-s` and original slice
  `d` at `s`.
- `integrableOn_quotientNormProfile_reversedDual_iff` transports integrability
  of the separate real raw-norm profile between those same restricted measures.
- `ae_quotientFiberIntegrable_reversedDual_iff` transports the actual fiber
  condition almost everywhere. The proof uses `MeasurableEquiv.map_ae` and the
  exact restricted measure law, then the pointwise fiber equivalence. It
  requires no measurability assumption on the Prop-valued fiber predicate.

The first two proofs use `MeasurePreserving.integrable_comp_emb`, the measurable
embedding of the published homeomorphism, and equality of the composed actual
functions. None deduces integrability from an equality of total integral values.

`kernelAbsoluteIntegrable_restrict_reversedDual_iff` assembles precisely these
three conditions in the existing `KernelAbsoluteIntegrable` predicate. It uses
`lowerMeasure_restrict` on both size families to identify the restricted lower
measures with the lower transports of `νN` restricted to the corresponding
standard determinant slices. The standard measure is restricted at `-d` on
the dual side and at `d` on the original side. Compatibility of those restricted
measures is not asserted or needed.

## Zero-parameter coefficient reflection

Let `qF` denote the canonical residue cardinality, and let `a(d)` and `b(d)` be
the original complex and real zero-parameter coefficients. The final two
lemmas prove, for every integer `d`,

```text
reversedDualSliceCoefficient ... d = (qF : ℂ)^d * a(-d),
reversedDualNormProfileSliceCoefficient ... d = (qF : ℝ)^d * b(-d).
```

The implemented proof specializes complementary-parameter slice transport to
original parameter `s = 1` and original slice `-d`. The dual parameter then is
zero and its slice is `d`. The imported spectral-scaling identity turns the
original integral at `1` into its zero-parameter coefficient times
`(spectralPoint qF 1)^(-d)`. Since `spectralPoint qF 1 = (qF : ℂ)⁻¹`, integer
power identities give exactly `(qF : ℂ)^d`. The real proof applies the separate
profile scaling and uses `norm_zpow` and `Complex.norm_natCast` to obtain
`(qF : ℝ)^d`. This argument remains valid for negative `d` and uses no
cancellation of a bilateral Laurent-series action.

## Provenance and limits

All assertions are internal deductions from the imported actual conditional
kernel/quotient comparisons, the actual spectral slice laws, and the published
lower-duality and lower-measure restriction transport. No new theorem from the
literature is asserted. The module preserves the supplied measures and actual
section and test data throughout.

The equivalences assert no convergence by themselves. Coefficient reflection
is an equality of individual total slice integrals. This module proves no
whole-quotient convergence, Laurent functional equation, analytic continuation,
rational factor identification, polynomial divisibility, equal-rank boundary,
or final dominant-rank gamma/L statement. Those remain separate obligations.
