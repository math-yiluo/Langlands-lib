# Trace characters in the actual class-function algebra

Author: Worker 1284. This is an internal construction from the published universal representation matrix and actual invariant coordinate equalizer.

For an actual finite matrix representation `ρ` of an arbitrary affine group scheme over a field `k : Type u`, `traceCoordinate ρ` is the trace of its universal matrix, regarded as an element of the group's actual coordinate algebra. The published universal-matrix evaluation identity and the compatibility of trace with additive homomorphisms show that this coordinate evaluates to the matrix trace at every affine coefficient point.

The trace belongs to `ClassFunctions.algebra G`. The proof uses the published equivalence between the actual equalizer condition and invariance on all commutative coefficient algebras. The representation sends conjugation to conjugation by a matrix unit, and Mathlib's `Matrix.trace_units_conj` proves invariance. This argument includes nonreduced coefficient algebras and makes no density assumption about field-valued points.

`traceClassFunction ρ` packages this coordinate in the actual invariant subalgebra and exposes its evaluation equation. This construction does not establish the existence of representations of fundamental highest weight, algebraic independence, invariant generation, or the triangular restriction formula for a Steinberg product. Those remain separate obligations in the split Steinberg theorem.
