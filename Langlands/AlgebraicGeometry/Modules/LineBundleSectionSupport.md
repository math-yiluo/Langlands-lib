# Sections supported in an open subscheme

This module constructs the reduced closed complement of an open subscheme and
proves the section identities needed to use that complement in ampleness
reflection. The constructions and proofs are internal derived content from
Mathlib's ideal-sheaf subschemes and the Library's actual modules, sections,
tensor products and pullback comparisons. They assume no cohomology comparison
or descent certificate.

For an open `U` of a scheme `X`, `closedComplement U` is the subscheme of the
vanishing ideal of the closed set `U.compl`. Its morphism `closedComplementι U`
is a closed immersion, has set-theoretic image exactly the complement of `U`,
and has quasi-compact source whenever `X` is quasi-compact. This uses the closed
complement `U.compl`, not the pseudocomplement in the lattice of opens.

The actual section identities are:

- `pullback_tensorSection`: the canonical pullback tensor comparison takes the
  pullback of a product section to the product of its two pulled-back factors.
  Its proof applies the section/morphism equivalence, naturality of the tensor
  comparison, and the published left-unit coherence. Unit naturality identifies
  the section of the tensor unit on both sides.
- `actualPullbackTensorPowIso_sectionPow`: the canonical actual tensor-power
  comparison takes the pullback of an actual power section to the corresponding
  power of the pulled-back section. This follows by induction, using the unit
  comparison in degree zero and the product identity at the successor step.

For any morphism `f : Y ⟶ X` with quasi-compact source, an empty inverse image
of a line-bundle section's whole generation open implies that some positive
power of the section pulls back to zero. This is
`exists_pos_pullback_sectionPow_eq_zero`. The proof identifies the generation
open of the actual pulled-back section, applies the companion nilpotence theorem
`exists_pos_sectionPow_eq_zero_of_trivializationOpen_eq_bot`, and uses the
power comparison isomorphism to reflect zero. In particular, the source need
not be reduced; this matters after inseparable field base change.

The closed complement has two useful support consequences. First,
`trivializationOpen_le_of_closedComplement_vanishing` says that a section which
pulls back to zero on this complement has its entire generation open contained
in `U`. The image formula and the published vanishing-locus lemma prove this
pointwise. Second, `closedComplement_preimage_trivializationOpen_eq_bot` says
that a section whose generation open lies in `U` has empty generation open on
the complement. Combining the latter fact with the general pullback nilpotence
result proves `exists_pos_sectionPow_closedComplement_eq_zero`: on a
quasi-compact `X`, such a section has some positive actual tensor power
vanishing on the closed complement.

No separatedness, noetherian or finite-type hypothesis is imposed in this
module. These constructions supply the support step of the intended
fixed-bundle reflection argument. The module does not prove that reflection
statement or assert a scalar extension comparison for global sections.
