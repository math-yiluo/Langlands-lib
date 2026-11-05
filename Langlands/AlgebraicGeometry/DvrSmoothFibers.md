# Smoothness from the actual generic and special fibres over a DVR

This is an internal comparison and smoothness prerequisite. It derives its
results from the published DVR point classification, the published comparison
with a chosen fraction field, and Mathlib's flat fibrewise smoothness criterion.
It uses no additional external mathematical source.

`closedPointResidueSpecIso` identifies the spectrum of the actual quotient
residue field of a local ring with the spectrum of the scheme residue field
at its closed point. It combines the canonical isomorphism from the maximal
ideal quotient to the ideal residue field with the canonical comparison
between ideal and scheme residue fields. The next theorem checks that this
isomorphism commutes with the original base map and the actual residue quotient.

`smooth_pullback_comp_right` proves stability under a second coefficient map
by the canonical iterated-pullback isomorphism. The private comparison lemma
applies it to the inverse of an isomorphism between a supplied coefficient
scheme and the corresponding scheme residue field.

`smooth_of_generic_special_fibers` considers a flat, locally finite-type
scheme morphism over a DVR, together with smoothness of its actual pullbacks
to a chosen fraction field and to the quotient residue field. The DVR is
Noetherian, so the morphism is locally of finite presentation. Every point
of its spectrum is generic or closed. The two coefficient comparisons
therefore give smoothness of every scheme residue fibre, and Mathlib's
`Smooth.of_smooth_fiberToSpecResidueField` proves smoothness of the original
morphism. No smoothness assumption on that original morphism is introduced.
