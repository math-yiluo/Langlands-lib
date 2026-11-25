# Trace of a trace-class integral operator as a diagonal integral

`Langlands.Analysis.OperatorIdeals.TraceClassContinuousKernelDiagonalStatement`
is a `Prop`-valued definition. This module states the result and supplies no proof.

## Statement

Let `X : Type u` have a second-countable topology and its Borel σ-algebra, and
let `μ` be a σ-finite measure on `X`. Let
`T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` be a bounded complex-linear operator and
`K : X → X → ℂ` a function. Assume:

1. `IsTraceClass T`.
2. `MemLp (Function.uncurry K) 2 (μ.prod μ)`: the kernel is almost everywhere
   strongly measurable and square integrable for the product measure.
3. For every `φ : Lp ℂ 2 μ`, the representative of `T φ` agrees
   `μ`-almost everywhere with `x ↦ ∫ y, K x y * φ y ∂μ`.
4. For `μ`-almost every `x`, `Function.uncurry K` is continuous at `(x, x)`
   for the product topology.

Then `x ↦ K x x` is `μ`-integrable and
`operatorTrace T = ∫ x, K x x ∂μ`.

The space is Mathlib's `Lp ℂ 2 μ`, and the integral is the Bochner integral.
The kernel is supplied with its defining integral formula. The conclusion
concerns this supplied representative. Continuity of its restriction to the
diagonal alone would be a different hypothesis: here continuity is at the
diagonal point in the entire product space. No compactness, finite measure,
metric, separation axiom, or continuity away from the diagonal is assumed.

## Trace conventions

The predicate `Langlands.Analysis.OperatorIdeals.IsTraceClass`, imported through
`OperatorTrace` from `OperatorIdeals`, asks for a Hilbert basis on which the
real diagonal of the positive left modulus `sqrt(T T*)` is summable.

`Langlands.Analysis.OperatorIdeals.operatorTrace` is defined in
`Langlands/Analysis/OperatorTrace.lean` as `traceIn` in one chosen Hilbert basis:
the complex sum of `inner ℂ (b i) (T (b i))`. The published theorem
`Langlands.Analysis.OperatorIdeals.operatorTraceBasis` in `OperatorTraceProof`
identifies this trace with the absolutely convergent diagonal sum in every
Hilbert basis when `IsTraceClass T` holds. This statement introduces no new
trace-class predicate, trace, or function space.

## Source and correspondence

C. Brislawn, *Traceable integral kernels on countably generated measure spaces*,
Pacific Journal of Mathematics **150** (1991), no. 2, 229–240, published version.
Registered source: `brislawn-1991-traceable-integral-kernels`; original publication:
<https://msp.org/pjm/1991/150-2/p03.xhtml>. The retained PDF has SHA-256
`c985964e1923282f40564248ecf6e7ae01ddfb165cc3cd8460031f9bcdc0df12`.
One-based PDF page numbers equal printed page numbers minus 227.

- **Corollary 3.2, printed p. 237 (PDF p. 10)** gives the trace formula for a
  trace-class operator on `L²(X, μ)`, with `μ` σ-finite Borel and `X` second
  countable, when the kernel is continuous at almost every diagonal point.
  These are the topology, measure, trace-class, and continuity hypotheses above.
- **Theorem 3.1, printed p. 235 (PDF p. 8), with its proof on pp. 236–237
  (PDF pp. 9–10)** gives an almost everywhere defined averaged diagonal and
  expresses the trace as its integral. The theorem states integrability of the
  maximal average on the diagonal; its proof also establishes absolute `L¹`
  convergence of the diagonal expansion, hence integrability of the averaged
  diagonal itself.
- **Theorem 2.4, printed p. 234 (PDF p. 7), especially (2.11)** identifies the
  averaged diagonal with `K(x, x)` almost everywhere under the continuity
  hypothesis. Transferring Theorem 3.1's integrability and trace formula through
  this identification gives both conjuncts of the Lean conclusion. This is the
  route used by Brislawn to obtain Corollary 3.2.

Section 3 works with a countably generated σ-finite measure space and an `L²`
kernel for a trace-class operator. A second-countable space has a countably
generated Borel σ-algebra. The Lean statement supplies the kernel explicitly
via hypotheses 2 and 3; it does not assert existence of a kernel. Brislawn's
second-countable setting requires no separation axiom, and neither does this
statement.

The Lean proposition provides the diagonal-integral step used by the abstract
simple twisted trace formula (in
`Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceProof`).
