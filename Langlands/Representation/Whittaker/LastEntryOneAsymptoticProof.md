# Last-entry-one Whittaker expansion

Author: Worker 186.

`Langlands.whittakerLastEntryOneAsymptotic` proves the entire closed
`Langlands.WhittakerLastEntryOneAsymptoticStatement.{uF,uV}`. The field and
representation-carrier universes remain independent. The target and every
pair it imports are unchanged.

## Scope

The theorem retains every prime, p-adic field with canonical topology, and
rank `n + 1`, including `n = 0`. It takes the target's continuous nontrivial
unit-norm additive character, admissible representation finitely generated
over its group algebra, and nonzero one-dimensional space of equivariant
algebraic Whittaker functionals. Reducible representations are allowed.

One finite set of continuous translation-finite functions on the full
diagonal torus is chosen before both the functional and vector. For every
such functional and vector, its coefficients are actual
`HarmonicAnalysis.SchwartzBruhat (Fin n → F.Carrier)` functions on all
additive `Fⁿ`. The identity holds at every diagonal whose last entry is one,
using the target's exact diagonal homomorphism and consecutive quotients.

## Implemented proof

Install the canonical topology and choose the spanning Whittaker functional
`ℓ₀` from the target hypothesis. `rootCoefficientSpace` is the actual image
of

```text
v ↦ (x ↦ ℓ₀ (ρ (diag(x₁⋯xₙ, x₂⋯xₙ, …, xₙ, 1)) v)).
```

This is a translation-stable subspace of scalar functions on the root
torus. The corestricted coefficient map is surjective onto this image.
The proof establishes the three hypotheses of
`Whittaker.jpsDecomposition` for this space as follows.

1. `rootCoefficientSpace_isLocallyConstantSpace` uses smoothness, obtained
   from admissibility. Pull the representation back along the continuous
   cumulative-product diagonal homomorphism. Each orbit map is locally
   constant, and composition with the algebraic functional preserves local
   constancy. No topology on the original carrier is needed.
2. `rootCoefficientSpace_hasCoordinateUpperSupport` uses the published
   `Whittaker.smoothSimpleRootSupport`. The adapters bundle the raw character
   and entrywise covariance, compare the diagonal homomorphisms, and apply
   the theorem with integral factor one. Evaluation at the cumulative-product
   section gives a bound before all root-coordinate tuples. The supplied
   topology is specialized to the canonical topological data used throughout.
3. `rootCoefficientSpace_finiteOperatorSpans` uses the published
   `Whittaker.coordinateJacquetKernelStatement` and
   `Parabolic.jacquetCenterSpan`. For each coordinate, the first theorem
   makes the actual Jacquet kernel vanish uniformly in every other
   coordinate. Thus the actual unnormalized two-block Jacquet quotient
   surjects onto the coordinate germ. The cumulative-product lift of a
   coordinate dilation is explicitly identified with the embedded block
   scalar `(b,1)`, making this surjection an intertwiner. Restrict the finite
   operator span of all block scalars to these tuples and descend it through
   the surjection. This proves the finite operator span of the actual germ
   action.

The center-span proof supplies the normalization and Jacquet finiteness
results behind step 3. A scalar central character of the coefficient image
is not used to obtain that operator span. `LastEntryOneAdapters` also proves
finite generation and admissibility of the full coefficient image via its
actual surjective coefficient intertwiner; the final proof applies the
kernel and center-span results directly to the original representation.

The published `Whittaker.jpsDecomposition` now chooses one root-torus finite
family for the whole coefficient space. Its independent uniform dilation
prerequisite retains `|b| ≤ 1` and a positive threshold before the entire
torus tuple and every allowed `b`. Its assembly theorem supplies
Schwartz–Bruhat functions on the whole additive space, including coordinate
hyperplanes. Neither dilation nor decomposition is an additional premise
of the present theorem.

`WhittakerLastEntryOne.assemble` pulls the root finite family back along the
continuous consecutive-quotient homomorphism. The published finite-function
closure theorem proves continuity and translation finiteness of these
pullbacks. The cumulative-product section is a right inverse, so pullback
is injective and `Finset.sum_image` has no collisions. Its other inverse
identity recovers every diagonal with last entry one. Finally, write any
equivariant functional as `c • ℓ₀` and scale its Schwartz–Bruhat coefficients
by `c`. This preserves the finite set and places its choice before both
the functional and vector.

The argument uses no positive-rank case restriction. The coordinate lemmas
and published decomposition include `n = 0`; the root torus and additive
space then have one point, and the last-entry-one diagonal is the identity.

## Modules and provenance

The submitted helper pairs are `LastEntryOneAssembly`, `LastEntryOneAdapters`,
and `LastEntryOneGerms`. Their Markdown describes the coordinate, topology,
coefficient, quotient, and operator-span constructions in detail. They are
derived internal arguments for applying the published JPS function-space
theorem to the target, rather than additional assumptions.

The principal published proof imports, directly or through those helpers,
are:

- `Langlands.Representation.Whittaker.JPSDecompositionProof`,
  theorem `Langlands.Whittaker.jpsDecomposition`.
- `Langlands.Representation.Whittaker.SmoothSimpleRootSupportProof`,
  theorem `Langlands.Whittaker.smoothSimpleRootSupport`.
- `Langlands.Representation.Whittaker.CoordinateJacquetKernelProof`,
  theorem `Langlands.Whittaker.coordinateJacquetKernelStatement`.
- `Langlands.Representation.Parabolic.JacquetCenterSpanProof`,
  theorem `Langlands.Parabolic.jacquetCenterSpan`.
- `Langlands.Representation.RankinSelberg.RootCoordinateProof` and
  `Langlands.Representation.RankinSelberg.FiniteFunctionClosureProof`.

The function-space definitions and statement were independently published
before their proof. The substantial kernel, center-span, support and JPS
proofs are independently accepted and published dependencies. In particular,
the uniform small-coordinate dilation and Schwartz–Bruhat assembly
statements and their separate exact proofs were published before the JPS
decomposition proof. The final theorem adds no supplied expansion or
unproved statement premise.

The original is H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
*Automorphic forms on GL(3) I*, Ann. of Math. (2) 109 (1979), 169–212,
registered source `jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Proposition (2.2), its proof, Lemma (2.2.1), and Remark (2.2.5), printed
pp.181–183 (one-based PDF14–16), were read in text and images during this
task. The finite-type extension motivates using the coefficient image for
a reducible representation. The full-torus functions in the conclusion are
the derived pullbacks explained in the published statement's Markdown;
only the last-entry-one expansion is proved here.

The checked project literature index and available errata-note locations
contained no source-specific correction. The proof uses the published
uniform-region dilation and coordinate-set assembly route described in
`JPSDecompositionProof.md`, rather than relying on the source's implicit
slice-family uniformity argument.
