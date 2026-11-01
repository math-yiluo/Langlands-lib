# Smooth adelic block-factor sections in a genuine normed tensor model

Author: Worker 2. Provenance: internal construction using the published actual
block tensor action, representation transport and adelic section APIs, and
Mathlib's indexed tensor basis. No new original-literature identification is made.

Let `F : Type uF` be any number field, `n` any natural rank and `B` a positive
ordered block shape, including the empty shape in rank zero. Each actual adelic
block has a complex linear representation `σ i` on a complex module
`V i : Type uV`. A normed complex space `E : Type uE` and an actual complex
linear equivalence `e : PiTensorProduct ℂ V ≃ₗ[ℂ] E` are explicit inputs.
The universes of the field, coefficient family and normed model are independent.
No topology on the original coefficient family or indexed tensor is required.

## The actual coefficient action and section transport

`coefficientAction` reuses `Langlands.transportRepresentation` to conjugate
the published `B.blockTensor σ` by `e`. The actual full adelic Levi acts on
`E` by `v ↦ e(blockTensor σ m (e⁻¹ v))`. `coefficientEquiv` is the published
transport equivalence, with underlying linear equivalence `e`. The displayed
pure-tensor formula follows from `blockTensor_tprod` and inverse cancellation.
Continuity of this Levi action is not an input or a conclusion.

`sectionEquiv` postcomposes genuine covariant tensor-valued sections by `e`;
its inverse postcomposes by `e⁻¹`. These are actual equivalences of full
adelic right-translation representations, retaining the constructed positive
half character in the covariance. `finiteSectionEquiv` restricts this
equivalence to sections with one common open finite stabilizer. Both maps
preserve the original stabilizer. The inverse laws are proved on actual
function values using the two inverse laws of `e`.

## Smooth sections and the faithful algebraic bridge

`SmoothSections` and `smoothInduced` use the published genuine normed
coefficient section construction with `coefficientAction`. Sections have one
common open finite stabilizer and real-smooth infinite slices valued in `E`.
Right translation is the full adelic action. `CompactOpenSections` uses the
published dedicated copy of this carrier, with its topology induced by the
faithful realization in actual continuous `E`-valued functions.

`toTensorSections` composes the faithful smooth-section inclusion with inverse
coefficient transport. It is an injective full adelic intertwiner into the
original algebraic tensor-valued covariant functions and evaluates as
`e⁻¹(f(x))`. Its image consists exactly of the algebraic sections which have
one common open finite stabilizer and whose infinite slices become real
smooth after applying `e`. The finite condition follows by inverse
`finiteSectionEquiv`; the infinite condition follows from cancellation in
the existing smooth-slice membership. `ofTensorSection` constructs the
inverse on this image from these two explicit regularity conditions.
`mem_range_toTensorSections` proves both directions of this exact image
criterion. No regularity is asserted for an arbitrary algebraic section.

## Compatible continuous changes of model

Given a second normed complex space `W : Type uW` and an actual equivalence
`e' : PiTensorProduct ℂ V ≃ₗ[ℂ] W`, `modelChange` is the equivalence of Levi
representations obtained by composing `coefficientEquiv e` inversely with
`coefficientEquiv e'`. It evaluates as `v ↦ e'(e⁻¹(v))`; its inverse evaluates
as `w ↦ e(e'⁻¹(w))`. No topology on the original tensor is involved.

If both of these actual maps between the normed models are continuous,
`compactOpenModelEquiv` is a continuous complex linear equivalence of the
actual compact-open smooth-section spaces. It applies the published
continuous coefficient postcomposition map in each direction. Its inverse
laws follow by injectivity of the continuous-function realization and the
coefficient inverse laws at each point. Its two continuity fields are the
published continuity results for those coefficient maps.

The evaluation formula is postcomposition by `e' ∘ e⁻¹`, and
`compactOpenModelEquiv_rightAction` proves equivariance for full adelic right
translation using the existing coefficient-map intertwining law.
`toTensorSections_modelChange` proves that the underlying algebraic tensor
section is unchanged: pointwise this is cancellation of `e'⁻¹ ∘ e'`.
Continuity of these two changes of model is an explicit hypothesis; no
equivalence of arbitrary tensor norms is asserted.

## A concrete finite-coordinate model

For finite coordinate index types `κ i : Type uK`, `coordinateEquiv` constructs
an actual equivalence

`PiTensorProduct ℂ (fun i => κ i → ℂ) ≃ₗ[ℂ] ((∀ i, κ i) → ℂ)`.

It is the coordinate map of the tensor product of the standard bases. The
target is an actual finite function space with its usual complex sup norm.
The pure-tensor formula is `v ↦ (p ↦ ∏ i, v i (p i))`, proved with Mathlib's
tensor-basis representation formula. Empty block shapes and empty coordinate
types are retained. This supplies a concrete model for these coefficient
families, without claiming a canonical norm for arbitrary algebraic tensors.

The construction supplies no nonzero sections, completed tensor product,
unitary completion, Haar-modulus identification, automorphic occurrence,
isobaric classification or tensor factorization of an automorphic representation.
No completeness, finite dimension or irreducibility is required of `E`.
