# Compact conjugation averaging of actual smooth kernels

`Langlands.Global.ArchimedeanGL.CompactKernelConjugationAverageStatement`
is an internal proposition defining one averaging obligation. This module
contains the statement and a parameter-shape example; it does not prove the
proposition. It retains every number field `K : Type u` and natural rank `n`,
including zero.

Write `G = InfiniteAdelicGL K n` and
`C = standardInfiniteCompact K n`. Both carry their existing topologies.
The latter is the actual subgroup assembled from real orthogonal and complex
unitary matrices. Its compactness is already proved in `ArchimedeanCompact`.
The input and output kernels belong to the published `SmoothCompactKernel`
subtype of actual smooth complex functions on `G`.

For every Borel-compatible measurable structure on `G`, every left Haar
measure `μ` on `G`, every Borel-compatible measurable structure on `C`,
every probability left Haar measure `ν` on `C`, and every compact smooth
kernel `κ`, the proposition asks for a compact smooth kernel `η` satisfying
all six conditions:

1. At every point of `G`, its value is the actual complex Bochner integral

   ```text
   η(x) = ∫ k : C, κ(k⁻¹ x k) dν(k).
   ```

2. Its closed support is contained in the compact conjugation saturation

   ```text
   { k y k⁻¹ | k ∈ C, y ∈ tsupport κ }.
   ```

   The Lean set uses a subgroup element `k : C` and a point
   `y ∈ tsupport κ`; its equality is `x = k.val * y * k.val⁻¹`.

3. It is invariant under conjugation by every element of the actual compact
   subgroup: `η(k⁻¹ x k) = η(x)`.
4. Its value at the identity equals the original kernel's value there.
5. If every value of `κ` is real and nonnegative, the same holds for `η`.
6. Its inverse-kernel integral against the same ambient Haar measure is
   unchanged:

   ```text
   ∫ x, η(x⁻¹) dμ(x) = ∫ x, κ(x⁻¹) dμ(x).
   ```

These are conclusions, rather than certificates supplied with `κ`.
In particular, genuine smoothness of the displayed average, compactness of
its closed support, and the integral identity must be proved. The pointwise
formula uniquely determines the underlying function; no chosen averaging
operator is introduced here. The statement asks for this average for every
complex kernel, not only for kernels already satisfying positivity or
normalization. Conditions 4–6 ensure that real nonnegativity, strict
positivity at the identity, and inverse integral one are all preserved when
the input has those properties.

The probability normalization of `ν` is explicit. Constructing such a
measure from finite nonzero Haar measure on the actual compact group is a
separate application of Haar measure theory; this module neither constructs
nor assumes a changed topology on that group. No right invariance,
inversion invariance, or unimodularity hypothesis is imposed on `μ`. A proof
of condition 6 must justify the needed changes of variables: conjugation by
members of a compact subgroup preserves ambient Haar integration, and
integration in `x` and `k` must be interchanged with valid integrability
arguments. None of those analytic steps is supplied as an extra premise.

The support bound deliberately permits enlargement to the compact
conjugation saturation. Turning it into a kernel supported in a prescribed
identity neighborhood requires a smaller neighborhood whose saturation is
contained there. Existence of normalized input kernels, this neighborhood
selection, derivative-topology approximation, compact-type projections and
preservation, and exact reproduction remain separate obligations.

This is a source-free internal prerequisite formulated against published
carriers and ordinary Haar integrals. It introduces no abstract reproducing
kernel assumption and asserts no automorphic differential-growth theorem.
