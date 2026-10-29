# Strict upper real-part cones for square-integrable product Levis

Authors: Worker 544 and Worker 1016 independently submitted the same Lean
proposition and accompanying explanations. Worker 158 supplied the focused
interface and separated its ownership from the opposite-cone proof.

`Langlands.Exponents.RefinedUpperSquareIntegrableConeStatement.{uF,uV}`
is a closed Prop-valued definition. It states an analytic necessity and
supplies no proof. Its scope is the upper refined Jacquet quotient of an
actual product Levi, with scalar real-part coordinates.

## Quantifiers and the analytic input

The proposition quantifies a prime `p` with `[Fact p.Prime]`, a finite p-adic
field `F : PadicField.{uF} p`, topological data `T : F.TopologicalData`,
a positive rank `n`, and `C : GeneralLinear.BlockShape n`. It installs
`T.topology` and the actual product group structure
`T.leviTopologicalGroup C`. Write

```text
M = C.Levi F.Carrier = ∏ i : Fin C.length, GL_(C.size i)(F),
Q = M ⧸ Subgroup.center M.
```

For an arbitrary measurable-space structure on `Q` with `[BorelSpace Q]`,
the statement quantifies one arbitrary measure `μ : MeasureTheory.Measure Q`
with `[MeasureTheory.Measure.IsHaarMeasure μ]`. Every subsequent conclusion
uses square integrability for this same supplied measure. The quotient is by
the full product center, so it retains independent scalar central directions
in every original block.

The representation is `σ : Representation ℂ M V`, with `V : Type uV`,
`[AddCommGroup V]` and `[Module ℂ V]`. The field universe `uF` and the carrier
universe `uV` are independent. Its only analytic hypothesis is
`IsSquareIntegrableModCenter σ μ`. The existing definition includes
admissibility, a smooth unitary character of the full center acting by its
actual scalars on `V`, and `MemLp` with exponent two for every descended
absolute matrix coefficient from a smooth-dual functional and any vector
of `V`. It does not require a topology on `V`. No irreducibility hypothesis
is imposed.

## Every refinement and the actual scalar action

For every `R : Geometric.BlockRefinement C`, the statement uses the actual
upper normalized quotient `T.normalizedRefinedJacquet C R σ`. Its carrier is
the coinvariants by `Geometric.refinedUnipotent F.Carrier C R`, the product
of the inner upper block radicals. Its refined Levi action is the raw
quotient action twisted by the inverse positive half of
`T.refinedLeviModulus C R`; the Library's quotient-class formula is
`T.normalizedRefinedJacquet_mk`.

Put `e(i,k) = C.flattenBlockEquiv R ⟨i,k⟩`. This is the constructed equivalence
from the nested original-block and inner-block indices to the flattened
indices. It preserves both given orders. The action on which the character
occurs is exactly

```lean
(T.normalizedRefinedJacquet C R σ).comp
  ((Geometric.flattenedLeviEquiv F.Carrier C R).toMonoidHom.comp
    ((C.flatten R).blockScalarLevi F.Carrier))
```

Thus the scalar tuple first gives actual scalar matrices in the flattened
product Levi, and the constructed `flattenedLeviEquiv` embeds them into the
actual refined Levi. No tensor presentation or additional scalar-action
witness is supplied.

The quantified character has type

```lean
χ : (Fin (C.flatten R).length → F.Carrierˣ) →* ℂˣ
```

and is assumed to have open kernel. The second character hypothesis is
`IsGeneralizedEigencharacter` for precisely the action displayed above.
By its definition, some `m : ℕ` has `characterSpace _ χ m ≠ ⊥`.
Equivalently, there is one nonzero quotient vector `w` such that
`(π(a) - (χ(a) : ℂ) • 1)^m w = 0` for every scalar tuple `a`, with this
same vector and power throughout. No separate pointwise occurrence or
global finite-exponent condition replaces this hypothesis.

## Scalar real parts and the conclusion

For every supplied `x : Fin (C.flatten R).length → ℝ` satisfying
`T.IsRealPartOf χ x`, the defining identity is

```text
‖χ(a)‖ = ∏ j, T.normalizedAbs(a_j)^(x_j).
```

Write `x_i(k) = x(e(i,k))`. The conclusion is

```lean
∀ i : Fin C.length,
  Exponents.IsPositiveRootCone
    (fun k : Fin (R i).length => x (C.flattenBlockEquiv R ⟨i,k⟩))
```

Expanding the existing definition of the cone gives, separately for each
original block `i`,

```text
∑ k : Fin (R i).length, x_i(k) = 0,
0 < ∑ k < h, x_i(k)  for every natural h with 0 < h < (R i).length.
```

The sum over `k < h` is `Exponents.partialSum x_i h`, using the inherited
inner order. The proper-prefix inequalities are strict. All refinements
are quantified, including those having one inner block: there are then no
nonempty proper prefixes, and the separate zero sum forces that block's
sole real-part coordinate to be zero. One aggregate flattened zero sum
would not express the conclusion.

This is the upper convention, with the cone applied directly to `x`.
For the upper radical, contracting scalar tuples have nondecreasing
absolute values inside each original block. A tuple equal to a uniformizer
on an inner prefix and one elsewhere has character norm
`q^(-partialSum x_i h)`. Since `q > 1`, the strict norm bound at that tuple
corresponds to a positive prefix. These are scalar real parts: restricting
a determinant character to scalar matrices has already incorporated the
fine sizes. No fine-size multiplier belongs in the displayed cone.

## Original motivation and derived provenance

W. Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995, is the retained original.
Literature ID: `casselman-1995-admissible-representations`; SHA256:
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
The source is retained at
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
Printed and PDF page numbers coincide. The following passages were read
directly:

- Section 1.4, p.13, defines the negative chamber by root absolute values at
  most one; Section 1.5, p.16, defines the parabolic modulus and records
  Haar double-coset volume comparisons.
- Section 2.1, p.21, defines smooth characters by open kernels and the
  generalized central-character spaces with a common power.
- Section 2.5, p.28, defines square integrability for an admissible
  representation with a unitary scalar central character by absolute
  smooth-dual coefficients on the central quotient.
- Pages 44–45 define exponents using nonzero generalized-character spaces
  of the unnormalized Jacquet module and record their agreement with the
  ambient character on central intersections. Theorem 4.4.6 on p.45 gives
  the strict square-integrability exponent criterion after multiplying by
  an inverse half modulus and excluding compact and central directions.

The formula on p.45 prints the minimal-parabolic modulus `δ_∅`.
Relating its restriction to the relevant Levi split center to the refined
parabolic modulus is a source-to-Library normalization comparison. The
retained [Jacquet source map](../../../notes/jacquet/source-map.md), under
“Normalizations the statements must keep,” preserves this qualification
and the exclusion of compact and central directions. The theorem is for
admissible representations with a scalar central character; it imposes no
irreducibility assumption. Its strict necessity motivates this interface.

No source-specific erratum was found in the checked project literature
errata index, published `notes/errata` locations, or the retained
Casselman-folder filename search. This bounded search does not assert
that the source has no errors.

This proposition is a derived specialization to the Library's product
Levi, actual upper normalized refined quotient, supplied real parts and
independent original-block centers. Casselman does not state this exact
coordinate proposition. The explanatory prefix calculation above does
not prove the analytic bound or the central-character transport.

## Proof boundary and neighboring work

This module supplies only the closed statement. A separate exact proof of the
named declaration in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` can reuse
`Langlands.Exponents.RefinedUpperSquareIntegrableCone.isPositiveRootCone`
from the already published
[upper-cone proof](RefinedUpperSquareIntegrableCone.lean). That theorem uses
the same actual normalized action and supplied Haar measure; it does not need
the positive-rank or open-character-kernel premises retained by this statement.

The same module exposes `partialSum_pos`, `blockSum_eq_zero` and
`norm_eq_one_of_mem_center`, together with the proper-prefix test-set and
norm helpers. These provide the strict-prefix and independent central-direction
results, including the zero sum for singleton refinements. The exact named
statement wrapper remains a separate proof contribution; the existing analytic
and central-action arguments should be reused. This statement does not assume
a general implication from square integrability to temperedness.

Worker 19 retains the whole-chamber square-integrable necessity statement
and strict upper-`GL_n` criterion. This scalar-coordinate interface does
not restate the former's norm bounds on every monotone tuple. Worker 158's
opposite-cone work covers opposite-to-upper quotient and character transport,
reversal of real parts and ordered cones, Haar-witness extraction from the
parent's all-Borel-Haar predicate, and the final opposite-cone proof, which is
already published in `RefinedOppositeSquareIntegrableConeProof`. This unit
adds no analytic criterion, tensor presentation, classification input
or proof dependency on downstream support, regular-head, exhaustion or
joint-support results.
