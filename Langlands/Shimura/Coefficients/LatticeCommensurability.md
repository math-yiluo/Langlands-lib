# Scalar comparisons between full lattices

Author: Worker 57. This is an internal deduction from the published lattice
definitions and denominator-clearing lemma. It concerns integral coefficient
modules, independently of any Shimura-space existence assertion.

Let `R` be a commutative integral domain, `K` its fraction field, and `V` a
`K`-module with the compatible `R`-module structure. A full lattice means
Mathlib's `Submodule.IsLattice K`: finite generation over `R` and full `K`-span.
No principal ideal, discreteness, topology, or finite residue field is assumed.

`exists_nonzero_smul_mem_finset` multiplies bounds for a finite list of vectors.
`exists_nonzero_smul_mem_of_fg` applies the published
`P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.KrullAkizukiLa.exists_smul_mem_span`
to each finite generator of a submodule `M`, using the full span of a lattice
`N`. A common product bounds all generators, and linearity then bounds `M`.
The published lemma is imported unchanged, not copied from its former draft.

`lattices_scalar_commensurable` applies this in both directions and multiplies
the resulting scalars. Thus there exists a single nonzero `r : R` satisfying
`r M ⊆ N` and `r N ⊆ M`. This is scalar commensurability; it makes no assertion
that either lattice quotient has a finite underlying set.

`latticeComparisonScalar` chooses such a proved bound. Its nonzero, forward
and backward theorems are the corresponding proved properties.
`latticeScaledComparison` and `latticeScaledComparisonBack` are actual linear
maps between the lattice subtypes, both multiplying the original ambient vector
by this same scalar. Their component formulas record that interpretation.
Their two composites are multiplication by `r * r` on the respective lattices.
Both maps are injective, because `r` has a nonzero image in `K` and scalar
multiplication by a nonzero field element is injective on `V`.

The chosen scalar is not asserted symmetric in the ordered pair or natural
under additional maps. This unit constructs scalar comparisons and proves their
intrinsic properties. Tensor rationalization, adelic product assembly, reduced
systems, associated sheaves, Hecke compatibility, and the host task's geometric
existence obligations are separate.
