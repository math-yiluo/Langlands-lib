# The Harris CM base and the cocharacter reflex base

Author: Worker 57.

This internal construction supplies the scalar and scheme maps relating
the CM base used by the Harris numerical trace condition to the actual
cocharacter reflex base used by the determinant condition. It is derived
from the published reflex-field calculation and the existing section maps.
It assumes no canonical model, representability or Lie comparison.

The parameters are the actual central-simple unitary datum
`D : CentralSimpleUnitaryData E K A n`, with the rational algebra structures
and scalar towers displayed in Lean, an imaginary quadratic CM number
field `L`, a ring embedding `j : L →+* K`, a complex embedding
`τ₀ : L →+* ℂ`, and Harris signature charts `C` for the actual section
`harrisCMSection E j τ₀`. In this notation the totally real field is `E`,
the CM center is `K`, and the source's imaginary quadratic field is `L`.
The construction retains the exceptional rank-two, single-real-place case.

`harrisCocharacterReflexField_le_distinguishedImage` proves that the
actual cocharacter reflex field is contained in the image of
`C.distinguishedEmbedding : K →+* ℂ`. The proof identifies it with the
chart reflex field, uses the published inclusion in the fixed field of
the image's fixing subgroup, and applies the proved complex fixed-field
theorem. The construction uses those existing theorems without adding
a fixed-field assumption.

`harrisReflexToCM` composes the inclusion of intermediate fields with
the inverse of the distinguished embedding's equivalence onto its
field range. The theorem `distinguishedEmbedding_harrisReflexToCM`
proves that composing this rational algebra map with the distinguished
embedding is exactly the original inclusion in `ℂ`.
`harrisReflexToCM_unique` proves that this property determines the map,
using injectivity of the distinguished embedding.

When `3 ≤ n` or there is a second real place, the published reflex-field
equality with the distinguished image proves surjectivity of the scalar
map. `harrisReflexCMEquiv` then constructs a genuine rational algebra
equivalence using its injectivity and this surjectivity. Surjectivity is
not asserted without that hypothesis.

`harrisCMToReflexBase` takes the spectrum of this scalar map, giving
`Spec K → Spec (D.kottwitzCocharacterReflexField C)`.
`harrisCMToReflexBase_complex` proves that the distinguished complex point
commutes with this map by contravariant functoriality of spectrum and
the proved scalar identity.

For any actual scheme `S` over `Spec K`, with structure map `p`,
`harrisReflexStructure D C p` is its composite with
`harrisCMToReflexBase`. `harrisReflexStructure_comp` proves compatibility
with every actual morphism `f : T → S` by associativity.
The general lemma `secHom_postcomp_specMap` proves the induced equality
of ring maps on every open, using the naturality of `ΓSpecIso` and the
composition law for actual `appLE` maps. Its Harris specialization
`secHom_harrisReflexStructure` identifies every reflex scalar section
with the section obtained through `p` and `harrisReflexToCM`.

Finally, `harrisReflexSectionDeterminant_CM` proves that the existing
reflex determinant sections for this constructed reflex structure map
are precisely the CM-valued determinant coefficients mapped to
sections through `p`. The proof composes multivariate polynomial maps
using the equality of actual scalar-section maps.

The scalar construction and scheme maps follow from
`CocharacterReflexField`, `Reflex`, `ReflexGaloisProof` and Mathlib's
equivalence onto an algebra embedding's field range. The determinant
specialization uses `HodgeDeterminantReflex`, `LieDeterminantCondition`
and `ReflexSectionPullback`. This is an internal derived prerequisite;
it introduces no new assertion attributed to the original literature.
The existing source and sign conventions of those modules are retained.
It does not identify arbitrary independently supplied base morphisms,
prove that the central trace and full determinant conditions are
equivalent, construct the full Lie-plus compatibility condition, or
construct a representing scheme.
