# Constituent existence from an irreducible spanning family

This is a supporting algebraic unit for Renard VI.3.2(i). It proves an
implication from the separately published proposition definition
`Langlands.CuspidalSupport.RationalNormKernelFiniteRestrictionStatement`;
it does not prove or assume that closed proposition without an explicit
argument.

`exists_irreducible_of_spanning_family` works for a representation of an
arbitrary monoid over an arbitrary field, on a nontrivial carrier. If a
family of irreducible subrepresentations spans that carrier, its index type
cannot be empty: an empty supremum would make the bottom submodule equal
the top submodule. Choosing one index gives the required constituent. The
index type is arbitrary; finiteness and semisimplicity are unnecessary for
this implication.

`irreducibleConstituentOfSpanningFamily` is the corresponding choice
construction. Given the same representation, spanning family and proofs,
it returns a subrepresentation together with a proof of its irreducibility.
It uses `Classical.indefiniteDescription` on the preceding existence
theorem; no canonical constituent or computational choice is asserted.

`rationalNormKernelConstituent_of_finiteRestriction` specializes this fact
to the actual restriction of an irreducible smooth complex representation
of the rational points of a connected reductive group over any
nonarchimedean local field. It takes a proof of
`RationalNormKernelFiniteRestrictionStatement` as its explicit first
argument, extracts that statement's finite spanning family, and derives
nontriviality of the original carrier from ambient irreducibility using
Mathlib's irreducible group-algebra module instance and
`IsSimpleModule.nontrivial`. The topology is exactly
`rationalPointTopology F G.X`; the subgroup is exactly
`Plancherel.rationalCommonNormKernel G`; restriction retains the original
carrier. Field and carrier universes `u` and `uV` are independent.

The supporting implication records the constituent-existence step of the
proof of Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, Proposition VI.3.2(i), printed pp.143–144 / PDF
pp.149–150. The source first proves part (ii) and then decomposes the
restriction into its nonzero isotypic components. Here only the finite
spanning-family consequence of part (ii) is used. Its correspondence with
part (ii) is explained by the imported
`RationalNormKernelFiniteRestrictionStatement.md`. The source is registered
as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The general spanning-family lemma and its choice construction are
elementary derived content, not additional assertions attributed to Renard.

This module proves neither the closed finite-restriction proposition nor
the closed single-orbit proposition. The eventual exact single-orbit
proof must supply an independently published proof of part (ii) when
using this adapter.
