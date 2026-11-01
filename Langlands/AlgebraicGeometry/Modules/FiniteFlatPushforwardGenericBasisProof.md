# Generic trivialization with the native finite-flat rank

`finiteFlatPushforwardGenericBasis` proves the complete published statement.
First `finiteFlatPushforwardStructure` gives quasi-coherence and finite sections
of the actual pushforward `P = f_* O_X`. Choose an affine open containing the
specified point. Its function ring `A` is a Noetherian domain. The helper
`affineChartSectionsEquiv` identifies the global sections of the restriction to
the chart spectrum with `Γ(P,U)` by the actual restriction maps and proves that
the scalar actions agree. Thus this module `N` is finite and its finrank is the
native rank `f.finrank x`.

The helper `exists_free_tensor_away` uses finite presentation over the
Noetherian domain and descends a basis from its fraction field to a principal
localization `Ar` at a nonzero element. The localization/tensor equivalence and
base-change finrank comparison show that `Ar tensor_A N` is free with the same
finrank. The localization ring is a domain, so its spectrum is nonempty.

Compose the localization open immersion with the original affine chart. The
restriction-composition comparison and restriction/pullback comparison identify
the restricted actual sheaf with the pullback from the first spectrum.
`affinePullbackTildeIso`, followed by `extendScalarsAlgebraIso`, identifies this
pullback with the tilde of `Ar tensor_A N`. A finite basis, reindexed by
`ULift (Fin (f.finrank x))`, and `tildeFinsupp` identify it with the actual free
sheaf. The scalar-extension/algebra-tensor comparison is explicit because their
scalar actions agree propositionally rather than definitionally.

The composite open immersion has a nonempty affine image. Its isomorphism to
the corresponding open subscheme transports the trivialization to that open;
`pullbackObjFreeIso` preserves the free sheaf during this transport. The open
need not contain the original point. No positive-rank assumption is used, so
the construction includes rank zero. This is an internal derivation from the
published sheaf constructions and Mathlib localization and basis results; it
asserts no polarized numerical-rank formula.
