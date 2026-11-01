# Actual dominant kernels under reversed duality

This internal definition and support-lemma unit compares the actual dominant
raw, weighted, rectangle-integrated and lower-quotient kernels under reversed
duality. Every kernel comparison has the explicit premise
`TwoBlockDominantDualMatrixStatement`. The module does not prove that matrix
statement or either final dominant-rank gamma or L proposition.

## Inputs and the fixed section equivalence

The field `F : PadicField p` has its canonical topology, valuation, local-field
structure and Borel measurable structure. Its universe and the universe of the
dependent block carriers are independent. The two positive block sizes are
`m i + 1`, with sum `t + 1`. Each block has an arbitrary complex representation
`σ i`, assumed smooth when selecting the section equivalence. No irreducibility,
nonvanishing, factor certificate or Whittaker-type assumption is added.

`reversedDualSectionEquiv F h σ hσ` is chosen from the published
`twoBlockDualSectionJacquet` theorem. It is an actual representation equivalence
from the inverse-transpose pullback of the original normalized induced
representation to the normalized induction of the reversed inverse-transpose
block family. Sizes, carrier spaces, their additive and module structures, and
representations are all reversed. The choice is made before the character,
inverse block functionals, section, test function and additive Haar measure.

For any unitary additive character `ψ` and inverse block functionals `ell`, write
`ellD i = secondDualFunctional ψ (σ i.rev) (ell i.rev)` and `E` for this fixed
equivalence. `reversedDualSectionEquiv_scalar` extracts its scalar identity:

```text
scalarSection ellD (E f) g 1 =
  scalarSection ell f (w_(t+1) * inverseTranspose g) 1.
```

The proof uses the scalar clause of `Classical.choose_spec` for the same
published existential, so it does not choose a new equivalence after the
analytic inputs are given.

## Actual kernel identities

Here `r = t + (j + k + 1)`, with natural `j,k` that may independently be zero.
Thus the module treats the strictly dominant rectangular case. Set
`Tg = w_(t+1) * inverseTranspose g` and let `Drect` be the published
`dualRectangleEquiv m j k`. It exchanges the two reversed rectangles using
negative transpose and reversal of both indices. The dual side has rectangle
parameters `k,j` and rank equality `r = t + (k + j + 1)`.

The dual test is exactly `reversedDualTest hr ψ Wtest`. It is the first dual
Whittaker function right-translated by `rightWeyl hr`. In particular, its
evaluation retains the factor `P * rightWeyl hr` inside the large-group inverse
transpose. The comparison is not with an untranslated dual test.

`rawKernel_reversedDual` combines the scalar identity, involutivity of
`g ↦ Tg`, and the second clause of the assumed matrix statement:

```text
w_(r+1) * inverseTranspose (reversedMatrix h hr (Tg) xD yD)
  = matrix h hr g (Drect (xD,yD)).1 (Drect (xD,yD)).2.
```

This is applied to the actual five-block matrix; there is no replacement kernel
or representative-dependent choice. It yields equality of the unweighted
dual kernel at `Tg,xD,yD` and the original one at `g,Drect(xD,yD)`.

`kernel_reversedDual` multiplies this identity by the determinant weights and
uses `dualDeterminantWeight`. The dual parameter `1-s`, with exchanged rectangle
sizes, gives exactly the original weight at `s`, for every complex `s`:

```text
kernel ellD (E f) (reversedDualTest hr ψ Wtest) hrD (1-s) (Tg) xD yD
  = kernel ell f Wtest hr s g (Drect (xD,yD)).1 (Drect (xD,yD)).2.
```

## Rectangle integration and actual convergence predicates

The additive Haar measure `ν` is supplied arbitrarily. Both sides use the exact
published `rectangleMeasure` products constructed from that same `ν`; no
self-duality or normalization is assumed.

`representativeKernel_reversedDual` rewrites the complex integrand by the
weighted identity and applies `integral_dualRectangleEquiv`.
`representativeNormProfile_reversedDual` applies the same change of variables
to the norm of the actual raw weighted kernel before rectangle integration.
Both are equalities of total Bochner integrals and assert no convergence.
The real profile remains the integral of the raw norm, not the norm of the
complex rectangle integral.

Independently, `fiberIntegrable_reversedDual_iff` rewrites the actual
Bochner-integrability predicate and applies
`integrable_dualRectangleEquiv_iff`. This is a genuine two-way equivalence for
the original supplied product measures; it does not infer integrability from
an equality of total integral values.

## Lower-quotient descent

The module reuses the published geometric homeomorphism
`TwoBlockLowerFourier.lowerDuality F.Carrier h` from the original lower quotient
to that of the reversed family. Its representative formula is `[g] ↦ [Tg]`.
The three final lemmas are:

- `quotientKernel_reversedDual`, the complex equality at parameters `1-s,s`;
- `quotientNormProfile_reversedDual`, the separate real profile equality;
- `quotientFiberIntegrable_reversedDual_iff`, the actual fiber equivalence.

Each proof is quotient induction followed by `lowerDuality_mk` and the
corresponding representative lemma. The complex, real and Prop-valued objects
are the existing invariant descents, so no representative is selected.
No outer quotient measure or outer integral is used in this unit.

## Provenance and remaining obligations

All new assertions are internal deductions from the imported actual Jacquet
section equivalence, determinant and translated-test identities, signed
rectangle measure transport, quotient-kernel definitions and lower-duality
geometry. The matrix statement is explicitly assumed rather than discharged;
its proof is a separate prerequisite. This module introduces no new claim from
the literature.

The module proves neither slice nor whole-quotient convergence, outer measure
transport, coefficient reflection, a Laurent functional equation, rational
factor existence or factor comparison. It does not cover the equal-rank
boundary. Both final dominant-rank gamma/L propositions retain their full
original obligations.
