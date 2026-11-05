# Cohomology and section maps of ideal-adic layers

This derived helper specializes the canonical quotient-filtration sequence
to the actual ideal multiples of `IdealAdicQuotients`. For `f : X → Spec R`,
an actual structure-sheaf module `M`, and ideals `I ≤ J`, `layer f h M`
is the categorical cokernel of `IM → JM`, hence the actual layer `JM/IM`.
The definitions and conditional conclusions require no flatness, properness,
noetherianity or coherence.

The source motivation is the short exact sequences in Stacks Project
Lemma 30.21.3, in the registered snapshot
`stacks-noetherian-fibre-section-lifting-2026-11-03`, `02OF.txt`.
The source uses successive powers of a maximal ideal. The present
construction works for any inclusion of base ideals.

`compositeQuotientIso` identifies the cokernel of the composite
`IM → JM → M` with the already defined quotient `M/IM`, using the
proved equality of the composite with the canonical inclusion.
`compositeQuotientIso_hom_quotientMap` identifies the final arrow with
the actual `quotientMap`, by cancelling the cokernel projection.
`layerInclusion` is the resulting map `JM/IM → M/IM`; its projection
formula specifies it canonically.

`layerSequence` uses these actual arrows. `layerSequence_shortExact`
transports the generic quotient-filtration short exact sequence along
`compositeQuotientIso`, with identity maps on its outer terms.
`surjective_sections_quotientMap` applies the actual right-derived
sequence to relative global sections: vanishing of `H¹(JM/IM)` makes
the map on sections of `M/IM → M/JM` an epimorphism, hence a
surjective module homomorphism.
`isZero_cohomology_quotient` uses exactness in any fixed natural degree
to propagate vanishing from the layer and `M/JM` to `M/IM`.

`adicLayer f I M n` is `IⁿM/Iⁿ⁺¹M`, with the natural-number index
unshifted. `surjective_sections_adicTransition_succ` gives the
corresponding conditional surjectivity of the exact canonical
transition from quotient `n+1` to quotient `n`.
`surjective_sections_adicTransition` composes these adjacent maps,
using the proved composition law for the actual quotient maps, to
obtain surjectivity for every finite transition if every layer has
vanishing first cohomology.
The uniform Serre vanishing threshold, the closed-fibre comparison,
and the eventual fibre-section lifting theorem remain separate
obligations.
