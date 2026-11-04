# Compact-open Hecke actions on entire closed Hilbert tensor slices

Author: Worker 2.

This internal construction gives an actual unital Hecke corner action on
the compact-open fixed vectors of an entire closed tensor slice in the supplied
global positive-form Hilbert completion. The ambient completed action and
the whole closed slice need not be smooth.

## Generic construction and finite formula

`TensorHilbertHeckeAux.cornerAction` takes a complex representation `τ` of a
topological group, an invariant subrepresentation `S`, a Borel Haar measure
`μ`, and a compact open subgroup `K`. The group and module universes are
independent. It first uses the genuine integrated corner action on
`S ⊓ smoothSubrepresentation τ`. The published containment lemma proves this
intersection smooth. It conjugates the resulting algebra homomorphism by the
published actual-vector equivalence `fixedInfSmoothEquiv`. Its target is
exactly the fixed submodule of the original full `S`, with its original action.

`cornerAction_smooth` proves that the same actual-vector identification
intertwines every corner element, by the inverse law of the linear equivalence.
`cornerAction_eq_sum` identifies the resulting vector in the original ambient
module with the finite sum of the unchanged operators `τ g`, using the existing
`fixedLevelActionSamples`. Their points and coefficients depend on `μ`, `K`
and the corner element alone, independently of the representation and vector.
The proof projects the published smooth integrated-action finite-sampling
identity through the ambient subtype inclusion, then uses its sum and scalar
linearity. No topology, dimension bound or smoothness of the full ambient
module is required.

`cornerAction_factor` proves covariance under the generic `factorFixedEquiv`
for a supplied genuine representation equivalence from an original smooth
factor onto the ambient smooth intersection. The original factor carrier has
its own independent universe. The proof applies the published
`Hecke.cornerAction_equiv` on the smooth fixed spaces, then
`cornerAction_smooth` on the same actual-vector identification. The factor's
smoothness is explicit; admissibility can supply it in applications.

## Actual completed slice

`FiniteTensorPresentation.sliceHilbertCornerAction` specializes this algebra
homomorphism to the actual `sliceHilbertRange` in `b.HilbertCompletion`.
The acting group is `GL_n` over the actual finite completion, with its existing
matrix topology and Borel measurable structure. Its action is the original
completed global action restricted along actual local insertion.

The number field `F` and original factor carriers have independent universes;
coefficients are complex and every natural rank is included. A genuine finite
tensor presentation, a global invariant positive form, the tail, the Haar
measure and the compact open subgroup are explicit inputs. There is no
admissibility, irreducibility or nonzero-tail premise; zero slices are included.
The Haar measure is supplied and used in the existing convolution corner,
including its existing normalized compact-open unit. This unit chooses no
new Haar normalization.

## Provenance and limits

This is an internal derivation from the published open-fixed-vector equivalence,
intrinsic smooth-intersection construction, Hecke corner action, finite-sampling
identity, corner covariance and Mathlib endomorphism-algebra conjugation.
No new identification with
original literature is asserted. The construction does not assert existence
of its supplied presentation or form, spectral occurrence or decomposition,
whole-slice smoothness, boundedness of the Hecke operators, or a Bochner
integral on the entire Hilbert space.
