# Framed matrix-product compactness and actual Fourier-side integrability

This internal derived helper proves joint compact support and genuine Bochner
integrability on an upper-unipotent group times the full matrix space. The first
Schwartz–Bruhat test may have support meeting singular matrices. The second test
must have invertible frame throughout its topological support. The concrete
first-column frame satisfies that condition on the actual comparison box at
positive level.

All declarations are in
`Langlands.RankinSelberg.CompactWhittakerSynthesis`.

## General framed support bound

For a Hausdorff topological division field `K`, a matrix size `r`, and a closed
subgroup `H` of the actual general linear group whose elements have determinant
one, `hasCompactSupport_framed_matrix_product` assumes a continuous map `frame`
on square matrices with

```text
frame(u * X) = u * frame(X)       for u in H.
```

For two Schwartz–Bruhat tests `Φ₁, Φ₂`, it further assumes that `frame(X)` is
invertible for every `X` in the topological support of `Φ₂`. It proves compact
support of the actual function

```text
(u,X) ↦ Φ₁(u * X) Φ₂(X)
```

on `H × M_r(K)`. No invertibility premise is imposed on `X` or on the support of
`Φ₁`.

The proof sends the compact second support through `frame` and lifts that image
to a compact set `G₂` in `GL_r(K)`, using the matrix embedding and the stated
invertibility. The framed first support is compact in the ambient matrix space.
Restricting its determinant to the compact determinant image of `G₂` gives a
compact group set `G₁`, by `isCompact_matrixDetRestriction` from the
ProductIntegrability module. On the nonzero locus, equivariance and determinant
one give `u * g₂ ∈ G₁` for the lift `g₂` of `frame(X)`. Hence
`u ∈ G₁ * G₂⁻¹`. Closedness of `H` transfers this compact bound to the subgroup.
Its product with the second test's compact support bounds the joint support.

`integrable_weighted_framed_matrix_product` adds second countability of the
general linear group, Borel measurable spaces on `H` and the matrix space,
measures `μH, μM` finite on compact sets, and `SFinite μM`. For arbitrary
continuous complex functions `a` on `H` and `b` on the matrix space it proves

```text
Integrable ((u,X) ↦ a(u) Φ₁(u * X) Φ₂(X) b(X)) (μH.prod μM).
```

The proof derives second countability of `H`, uses the product Borel and
compact-finiteness instances, and applies continuous compact-support
integrability. The weights preserve the compact support just established.

## The concrete first-column frame

`firstColumnFrame n X` replaces column zero of an `(n+1) × (n+1)` matrix by
column zero of the identity. `firstColumnFrame_mul` proves equivariance under
actual upper-unipotent matrices: these matrices fix that identity column.
`continuous_firstColumnFrame` records continuity, and `det_firstColumnFrame`
identifies its determinant with the bottom-right `n × n` minor, by expansion
along column zero.

For canonical `F : PadicField p`,
`firstColumnFrame_mem_range_of_mem_box` proves that the frame is invertible
throughout `RankOneBox.box F A q a` for every `A,q : ℤ` and `0 < a`. Replacing
row zero of the frame by the identity row produces a matrix all of whose
entries differ from the identity by an element of `levelSet F.Carrier a`.
The principal-level-subgroup lifting theorem makes this matrix invertible.
Expansion along column zero shows that it and the frame have the same
determinant, proving the claim. This works for every `n : ℕ`, including `0`;
the proof does not require invertibility of the original matrix.

## Canonical measures, character, and Fubini

The p-adic section installs the field's canonical topology, valuation,
local-field structure, Hausdorff property and second countability, with the
Borel measurable spaces. Published general-linear and upper-unipotent
countability/local-compactness certificates supply the Haar hypotheses.

`integrable_unipotent_framed_matrix_product` specializes the general bound to
the actual upper-unipotent subgroup, its fixed `unipotentHaar`, and

```text
a(u) = ((standardCharacter ψ n u)⁻¹ : ℂˣ).val.
```

The full-matrix measure `μM` is supplied, with `SFinite μM` and finiteness on
compact sets, and `b` is any continuous complex weight on full matrices. The
frame hypothesis remains explicit.
`integrable_unipotent_box_matrix_product` supplies it from the assumption
`tsupport Φ₂ ⊆ RankOneBox.box F A q a` with `0 < a`.
`integral_unipotent_box_matrix_swap` exchanges the unipotent and full-matrix
integrals of exactly this weighted function by Fubini, using that genuine
product-integrability theorem.

`integrable_unipotent_box_rectangular_product` and
`integral_unipotent_box_rectangular_swap` take `b = 1` and precisely the supplied
`rectangularMeasure ν (n+1) (n+1)`, the additive product measure used in
`rectangularFourierIntegral`. They prove integrability and the actual exchange
for the function `a(u) Φ₁(u * X) Φ₂(X)`. No rescaling of `ν` or the unipotent
Haar occurs. These results hold for every supplied additive Haar measure and
`ψ : UnitaryAdditiveCharacter F.Carrier`. This character type already bundles
nontriviality; the support and Fubini proofs use its continuity without using
the nontriviality field and require no self-duality assumption.
They do not assert continuity of a determinant
power on singular matrices or identify such a power with the arbitrary weight.

## Provenance and scope

This is an internal derivation from the matrix embedding and determinant
restriction in ProductIntegrability, the existing comparison-box entry
conditions and principal-congruence lifting theorem, canonical topology and
countability certificates, and standard-character continuity. Mathlib supplies
compactness, matrix column operations, determinant expansion, continuous
compact-support integrability and Fubini. The accompanying ProductIntegrability
Markdown explicitly records the same bundled character hypothesis.

This helper establishes the convergence prerequisite useful after Fourier
transformation of the first test. It does not prove the Fourier endpoint,
construct the coefficient used there, or prove a gamma functional equation.
