# Polynomial annihilation for the actual Cartan square sum

Authors: Worker 94 and Worker 815. Module:
`Langlands.Global.ArchimedeanCartanPolynomialStatement`.

`Langlands.Global.ArchimedeanGL.CartanSquareSumPolynomialAnnihilationStatement K n`
is a proposition about the published actual smooth functions
`SmoothFunctions K n`, the joint differential orbit span
`jointOrbitSpan K n f`, the finiteness predicate `IsJointFinite K n f`,
the genuine differential action `envelopingAction K n` and the full
Cartan square sum `cartanSquareSum K n` from
`Langlands.Global.ArchimedeanCasimirCartan`. It is stated for an
arbitrary number field `K : Type u` and every natural rank `n`,
including `n = 0`. All original carriers, definitions, norms and
topologies are retained.

For each `f : SmoothFunctions K n` with `IsJointFinite K n f`, the
proposition asks for a complex polynomial `p` such that `p` is monic,
`p.natDegree = Module.finrank ℂ (jointOrbitSpan K n f)`, and

```text
envelopingAction K n (Polynomial.aeval (cartanSquareSum K n) p) g = 0
```

for every `g : SmoothFunctions K n` with `g ∈ jointOrbitSpan K n f`.
Polynomial evaluation takes place in the original complex universal
enveloping algebra `EnvelopingAlgebra K n`. A single polynomial
annihilates every vector of the whole joint orbit span; it may depend on
`f`, and no bound uniform over all functions is asserted. No centrality,
compact-invariance, positive-rank, nonzero-function or analytic
regularity hypothesis is added. When the joint orbit span is zero, the
required degree is zero, so the monic polynomial is `1`, and the
condition concerns only the zero vector; this case is retained.

## Provenance

This is an internal algebraic prerequisite, with no external theorem
attribution. It is the concrete specialization of the published generic
finite joint-orbit statement
`JointOrbitPolynomialAnnihilationStatement` (module
`Langlands.Global.ArchimedeanJointPolynomialStatement`), which concerns
the sum `centerInclusion K n z + b.val` for every central element `z`
and every element `b` of the actual compact enveloping subalgebra. The
published identity `cartanSquareSum_eq_central_add_compact` states

```text
cartanSquareSum K n = centerInclusion K n (matrixCentralCasimir K n)
  + (2 : ℂ) • (compactCartanElement K n : EnvelopingAlgebra K n),
```

so the actual Cartan square sum is the matrix trace Casimir in the
center plus twice the compact square sum. A prospective proof can apply
the generic statement with `z = matrixCentralCasimir K n` and
`b = (2 : ℂ) • compactCartanElement K n`, then rewrite with this
identity. Neither the generic statement nor the present one is proved
here.

## Scope

This module defines only the proposition; no proof is bundled with it,
and a separate exact-target proof task follows its publication. It
makes no assertion about ellipticity of a polynomial differential
operator, analytic regularity, analyticity of solutions, jets or jet
uniqueness, compact admissibility, orbit density, reproducing kernels
or the final automorphic differential-growth theorem. In particular,
the existence of such an annihilating polynomial is not asserted to
imply any of those analytic conclusions.
