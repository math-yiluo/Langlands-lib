# Ideal multiples with the Čech module scalar action

This internal comparison connects the actual ideal-multiple sheaf with
`OModulePresheaf.ofModules`, the coefficient model of the alternating Čech
complex. It imports `IdealAdicMultipleSections` without changing its
construction or hypotheses.

The base scalar `scalar f U r` is the same section as the algebra map
used by `Scheme.TwoAffineOpenCover.algebraOfHom`. Thus the base action on
`OModulePresheaf.ofModules` agrees with scalar multiplication in the
actual module sheaf. The definition `inclusionSections` equips the actual
inclusion on sections with this base-ring linear structure.

For every open, membership in the sectionwise span of ideal products is
equivalent to membership in `J • ⊤` for that base-ring action.
Span induction proves the forward implication. Its coefficient step
uses commutation of scalars to absorb a section-ring coefficient into the
module section of each ideal product. Induction on the ideal multiple
proves the converse. No finiteness or quasi-coherence is needed for this
algebraic comparison.

When the open is affine, the ideal is finitely generated and the module
is quasi-coherent, `range_inclusionSections` combines this comparison
with `mem_range_inclusion_app_iff` to identify the range of the actual
inclusion with `J • ⊤`. These are derived interface lemmas for the
stable-image proof; they do not establish a uniform cohomology estimate.
