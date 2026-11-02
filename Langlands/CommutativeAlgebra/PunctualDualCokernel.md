# The cokernel of the dual first differential

Author: Worker 413. Worker 1015 contributed the adapter interface for the
punctual-complex proof.

This is an internal linear-algebra construction using the order ideal defined
in `Langlands.CommutativeAlgebra.PunctualFirstDifferential` and Mathlib's
module quotient and cokernel constructions. It introduces no external-source
assertion.

For a commutative ring `R`, a cochain complex `L`, and an equivalence
`e₀ : L.X 0 ≃ₗ[R] R`, `rankOneDualEvaluation e₀` identifies the dual of
`L.X 0` with `R` by evaluating a functional at `e₀.symm 1`. It is the
composition of the dual of `e₀.symm` with the standard equivalence between
linear maps out of `R` and their values at `1`.

The dual of the first differential sends a functional `φ` on `L.X 1` to
`φ ∘ d⁰`. Evaluation at the chosen generator therefore sends it to
`φ (d⁰(e₀.symm 1))`. The lemma `dual_firstDifferential_range` identifies
the transported range with `firstDifferentialOrderIdeal L e₀`.

`firstDifferentialDualCokernelIsoQuotient` constructs an actual isomorphism
of `R`-modules from the categorical cokernel of
`ModuleCat.ofHom (L.d 0 1).hom.dualMap` to
`R / firstDifferentialOrderIdeal L e₀`. Its proof first uses
`ModuleCat.cokernelIsoRangeQuotient`, and then the quotient equivalence
induced by rank-one dual evaluation and the range identity.

For a local ring, `firstDifferentialDualCokernelIsoResidueField` specializes
this construction when the order ideal equals `maximalIdeal R`. Its target
is the actual `ResidueField R` with its canonical `R`-module structure.
The final theorem supplies the same isomorphism in `Nonempty` form.

These constructions require no freeness of the degree-one term, no support
bound, and no Noetherianity. The local-ring assumption is used only to name
the maximal ideal and residue field in the specialization. This pair supplies
the cokernel adapter for a separate reversed-dual complex construction; it
does not identify the cokernel with that complex's homology or prove the
final punctual-complex proposition.
